package com.ing.baker.runtime.model

import com.ing.baker.runtime.catseffect.AsyncSupport.toAsync
import com.ing.baker.runtime.catseffect.SyncSupport.syntax._
import com.ing.baker.il.{RecipeVisualStyle, RecipeVisualizer}
import com.ing.baker.runtime.catseffect.AsyncSupport
import com.ing.baker.runtime.common.BakerException.{ProcessAlreadyExistsException, ProcessDeletedException}
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, RecipeInstanceConfig}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult}

import scala.concurrent.duration.FiniteDuration
import java.util.concurrent.CompletableFuture
import java.util.concurrent.TimeoutException
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicReference
import scala.collection.mutable.ListBuffer

sealed trait RecipeInstanceStatus[F[_]]

object RecipeInstanceStatus {

  case class Active[F[_]](recipeInstance: RecipeInstance[F], lastModified: Long) extends RecipeInstanceStatus[F]

  case class Deleted[F[_]](recipeId: String, createdOn: Long, deletedOn: Long) extends RecipeInstanceStatus[F]
}

trait RecipeInstanceManager[F[_]] {

  private final class OneShotSignal[A](future: CompletableFuture[A]) {
    def complete(value: A)(implicit async: AsyncSupport[F]): F[Unit] =
      async.map(async.delay(future.complete(value)))(_ => ())

    def get(implicit async: AsyncSupport[F]): F[A] =
      async.fromCompletableFuture(async.delay(future))
  }

  private def oneShotSignal[A](implicit async: AsyncSupport[F]): F[OneShotSignal[A]] =
    async.delay(new OneShotSignal[A](new CompletableFuture[A]()))

  protected def store(newRecipeInstance: RecipeInstance[F])(implicit components: BakerComponents[F]): F[Unit]

  protected def fetch(recipeInstanceId: String): F[Option[RecipeInstanceStatus[F]]]

  protected def fetchAll: F[Map[String, RecipeInstanceStatus[F]]]

  def remove(recipeInstanceId: String): F[Unit]

  def idleStop(recipeInstanceId: String): F[Unit]

  def getAllRecipeInstancesMetadata: F[Set[RecipeInstanceMetadata]]

  protected def cleanupRecipeInstances(idleTimeOut: FiniteDuration)(implicit async: AsyncSupport[F]): F[Unit] =
    for {
      allRecipeInstances <- fetchAll
      _ <- allRecipeInstances.toList.foldLeft(async.unit) { case (acc, (recipeInstanceId, instance)) =>
        acc.flatMap(_ =>
          computeShouldDelete(instance, idleTimeOut).flatMap(shouldDelete =>
            if (shouldDelete) remove(recipeInstanceId) else async.unit))
      }
    } yield ()

  def bake(recipeId: String, recipeInstanceId: String, config: RecipeInstanceConfig)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    for {
      _ <- fetch(recipeInstanceId).flatMap[Unit] {
        case Some(RecipeInstanceStatus.Active(_, _)) =>
          async.raiseError(ProcessAlreadyExistsException(recipeInstanceId))
        case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
          async.raiseError(ProcessDeletedException(recipeInstanceId))
        case None =>
          async.unit
      }
      recipeInfo <- components.recipeManager.getRecipe(recipeId)
      newRecipeInstance <- RecipeInstance.empty[F](recipeInfo.compiledRecipe, recipeInstanceId, config)
      _ <- store(newRecipeInstance)
    } yield ()

  def hasRecipeInstance(recipeInstanceId: String)(implicit async: AsyncSupport[F]): F[Boolean] =
    fetch(recipeInstanceId).map(_.nonEmpty)

  def getRecipeInstanceState(recipeInstanceId: String)(implicit async: AsyncSupport[F]): F[RecipeInstanceState] =
    getExistent(recipeInstanceId).flatMap(
      _.state.get.map { currentState =>
        RecipeInstanceState(
          currentState.recipe.recipeId,
          recipeInstanceId,
          currentState.ingredients,
          currentState.recipeInstanceMetadata,
          currentState.events
        )
      })

  def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default)(implicit async: AsyncSupport[F]): F[String] =
    for {
      recipeInstance <- getExistent(recipeInstanceId)
      currentState <- recipeInstance.state.get
    } yield RecipeVisualizer.visualizeRecipe(
      currentState.recipe,
      style,
      eventNames = currentState.events.map(_.name).toSet,
      ingredientNames = currentState.ingredients.keySet
    )

  def fireEventStream(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Either[FireSensoryEventRejection, Vector[EventInstance]]] =
    async.delay(ListBuffer.empty[EventInstance]).flatMap { events =>
      fireEventAndProcess(recipeInstanceId, event, correlationId)(eventInstance => async.delay(events += eventInstance).map(_ => ()))
        .map(_.map(_ => events.toVector))
    }

  def fireEventAndProcess(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Either[FireSensoryEventRejection, Unit]] =
    fetch(recipeInstanceId).flatMap {
      case None =>
        async.pure(Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId)))
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        async.pure(Left(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId)))
      case Some(RecipeInstanceStatus.Active(recipeInstance, _)) =>
        recipeInstance.fireEventAndProcess(event, correlationId)(onEvent)
    }

  def fireSensoryEventAndAwaitReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[SensoryEventStatus] = {
    for {
      resolvedStatus <- async.delay(new CompletableFuture[SensoryEventStatus]())
      firstEventObserved <- async.delay(new AtomicBoolean(false))
      processing = fireEventAndProcess(recipeInstanceId, event, correlationId) { _ =>
        async.delay(firstEventObserved.compareAndSet(false, true)).flatMap { isFirst =>
          if (isFirst) async.delay(resolvedStatus.complete(SensoryEventStatus.Received)).map(_ => ())
          else async.unit
        }
      }.flatMap {
        case Left(rejection) =>
          async.attempt(foldToStatus((_: Unit) => async.unit)(Left(rejection))).flatMap {
            case Left(error) => async.delay(resolvedStatus.completeExceptionally(error)).map(_ => ())
            case Right(status) => async.delay(resolvedStatus.complete(status)).map(_ => ())
          }
        case Right(_) =>
          async.delay {
            if (!firstEventObserved.get) resolvedStatus.complete(SensoryEventStatus.Received)
          }.map(_ => ())
      }
      _ <- async.startAndForget(processing)
      status <- async.fromCompletableFuture(async.delay(resolvedStatus))
    } yield status
  }

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[SensoryEventStatus] =
    fireEventAndProcess(recipeInstanceId, event, correlationId)(_ => async.unit)
      .flatMap(foldToStatus(_ => async.unit))

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[SensoryEventResult] = {
    for {
      latestResult <- async.delay(new AtomicReference[SensoryEventResult](SensoryEventResult(SensoryEventStatus.Completed, Seq.empty, Map.empty)))
      outcome <- fireEventAndProcess(recipeInstanceId, event, correlationId)(eventInstance =>
        async.delay(latestResult.set(aggregateResult(latestResult.get, eventInstance))))
      result <- foldToResult((_: Unit) => async.pure(latestResult.get))(outcome)
    } yield result
  }

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[SensoryEventResult] = {
    for {
      latestResult <- async.delay(new AtomicReference[SensoryEventResult](SensoryEventResult(SensoryEventStatus.Completed, Seq.empty, Map.empty)))
      firstMatchingResult <- async.delay(new AtomicReference[Option[SensoryEventResult]](None))
      outcome <- fireEventAndProcess(recipeInstanceId, event, correlationId)(eventInstance =>
        async.delay {
          val next = aggregateResult(latestResult.get, eventInstance)
          latestResult.set(next)
          if (firstMatchingResult.get.isEmpty && next.eventNames.contains(onEvent)) {
            firstMatchingResult.set(Some(next))
          }
        })
      result <- foldToResult((_: Unit) => async.pure(firstMatchingResult.get.getOrElse(latestResult.get)))(outcome)
    } yield result
  }

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[(F[SensoryEventStatus], F[SensoryEventResult])] =
    async.delay(new AtomicReference[SensoryEventResult](SensoryEventResult(SensoryEventStatus.Completed, Seq.empty, Map.empty))).flatMap { latestResult =>
      fireEventAndProcess(recipeInstanceId, event, correlationId)(eventInstance =>
        async.delay(latestResult.set(aggregateResult(latestResult.get, eventInstance))))
        .map { outcome =>
          (
            foldToStatus((_: Unit) => async.unit)(outcome.map(_ => ())),
            foldToResult((_: Unit) => async.pure(latestResult.get))(outcome.map(_ => ()))
          )
        }
    }

  def addMetaData(recipeInstanceId: String, metadata: Map[String, String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] = {
    getExistent(recipeInstanceId).flatMap((recipeInstance: RecipeInstance[F]) => {
      recipeInstance.state.update(currentState => {
        val newRecipeInstanceMetaData = currentState.recipeInstanceMetadata ++ metadata
        currentState.copy(
          ingredients = currentState.ingredients + (RecipeInstanceMetadataName -> com.ing.baker.types.Converters.toValue(newRecipeInstanceMetaData)),
          recipeInstanceMetadata = newRecipeInstanceMetaData)
      })
    })
  }

  def awaitEvent(recipeInstanceId: String, eventName: String, timeout: FiniteDuration, waitForNext: Boolean = false)(implicit async: AsyncSupport[F]): F[Unit] =
    getExistent(recipeInstanceId).flatMap { recipeInstance =>
      oneShotSignal[Unit].flatMap { listener =>
        async.timeoutTo(
          recipeInstance.state.modify { currentState =>
            // If waitForNext is false, check if the event has already occurred
            if (!waitForNext && currentState.events.exists(_.name == eventName)) {
              (currentState, async.unit) // Already happened, resolve immediately
            } else {
              // Not yet happened (or waitForNext=true), add listener and wait on it
              (currentState.addEventListener(eventName, com.ing.baker.runtime.model.recipeinstance.RecipeInstanceState.Listener(listener.complete(()))), listener.get)
            }
          }.flatMap(x => x),
          timeout,
          async.raiseError(new TimeoutException(s"Timed out after $timeout waiting for event '$eventName' in instance '$recipeInstanceId'"))
        )
      }
    }

  def stopRetryingInteraction(recipeInstanceId: String, interactionName: String)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    getExistent(recipeInstanceId).flatMap(_.stopRetryingInteraction(interactionName))

  def retryBlockedInteraction(recipeInstanceId: String, interactionName: String)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Vector[EventInstance]] =
    async.delay(ListBuffer.empty[EventInstance]).flatMap { events =>
      retryBlockedInteractionAndProcess(recipeInstanceId, interactionName)(event => async.delay(events += event).map(_ => ()))
        .map(_ => events.toVector)
    }

  def retryBlockedInteractionAndProcess(recipeInstanceId: String, interactionName: String)(onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    getExistent(recipeInstanceId).flatMap(_.retryBlockedInteractionAndProcess(interactionName)(onEvent))

  def resolveBlockedInteraction(recipeInstanceId: String, interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Vector[EventInstance]] =
    async.delay(ListBuffer.empty[EventInstance]).flatMap { events =>
      resolveBlockedInteractionAndProcess(recipeInstanceId, interactionName, eventInstance)(event => async.delay(events += event).map(_ => ()))
        .map(_ => events.toVector)
    }

  def resolveBlockedInteractionAndProcess(recipeInstanceId: String, interactionName: String, eventInstance: EventInstance)(onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    getExistent(recipeInstanceId).flatMap(_.resolveBlockedInteractionAndProcess(interactionName, eventInstance)(onEvent))

  def awaitCompleted(recipeInstanceId: String, timeout: FiniteDuration)(implicit async: AsyncSupport[F]): F[SensoryEventStatus] =
    getExistent(recipeInstanceId).flatMap { recipeInstance =>
      oneShotSignal[Unit].flatMap { listener =>
        async.timeoutTo(
          recipeInstance.state.modify { currentState =>
            if (currentState.isInactive) {
              (currentState, async.pure(SensoryEventStatus.Completed)) // Already idle
            } else {
              // Not idle, add listener and then wait on it
              (currentState.addIdleListener(com.ing.baker.runtime.model.recipeinstance.RecipeInstanceState.Listener(listener.complete(()))), listener.get.map(_ => SensoryEventStatus.Completed))
            }
          }.flatMap(x => x),
          timeout,
          async.raiseError(new java.util.concurrent.TimeoutException(s"Timed out after $timeout waiting for instance '$recipeInstanceId' to become idle."))
        )
      }
    }

  private def getExistent(recipeInstanceId: String)(implicit async: AsyncSupport[F]): F[RecipeInstance[F]] =
    fetch(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(recipeInstance, _)) => async.pure(recipeInstance)
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) => async.raiseError(BakerException.ProcessDeletedException(recipeInstanceId))
      case None => async.raiseError(BakerException.NoSuchProcessException(recipeInstanceId))
    }

  private def aggregateResult(current: SensoryEventResult, event: EventInstance): SensoryEventResult =
    current.copy(
      eventNames = current.eventNames :+ event.name,
      ingredients = current.ingredients ++ event.providedIngredients)

  private def foldToStatus[A](f: A => F[Unit])(outcome: Either[FireSensoryEventRejection, A])(implicit async: AsyncSupport[F]): F[SensoryEventStatus] =
    outcome match {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        async.raiseError(BakerException.IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        async.raiseError(BakerException.NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        async.pure(SensoryEventStatus.FiringLimitMet)
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        async.pure(SensoryEventStatus.AlreadyReceived)
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        async.pure(SensoryEventStatus.ReceivePeriodExpired)
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        async.pure(SensoryEventStatus.RecipeInstanceDeleted)
      case Right(a) =>
        f(a).map(_ => SensoryEventStatus.Received)
    }

  private def foldToResult[A](f: A => F[SensoryEventResult])(outcome: Either[FireSensoryEventRejection, A])(implicit async: AsyncSupport[F]): F[SensoryEventResult] =
    outcome match {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        async.raiseError(BakerException.IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        async.raiseError(BakerException.NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        async.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        async.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        async.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        async.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(a) =>
        f(a)
    }

  private def computeShouldDelete(status: RecipeInstanceStatus[F], idleTimeOut: FiniteDuration)(implicit async: AsyncSupport[F]): F[Boolean] =
    for {
      currentTime <- async.pure(System.currentTimeMillis())
      result <- status match {
        case RecipeInstanceStatus.Active(recipeInstance, lastModified) =>
          recipeInstance.state.get.map { currentState =>
            //If the process is Inactive validate on the idleTTL
            val shouldPassivateOnIdleTTL = currentState.isInactive && currentTime > (lastModified + idleTimeOut.toMillis)
            //If the retentionPeriod is defined always delete after this time
            val shouldPassivateOnRetentionPeriod = currentState.recipe.retentionPeriod.exists(_.toMillis + currentState.createdOn < currentTime)
            shouldPassivateOnIdleTTL || shouldPassivateOnRetentionPeriod
          }
        case RecipeInstanceStatus.Deleted(_, _, _) =>
          async.pure(false)
      }
    } yield result
}