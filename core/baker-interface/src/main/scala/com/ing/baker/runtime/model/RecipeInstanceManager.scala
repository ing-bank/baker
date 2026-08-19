package com.ing.baker.runtime.model

import com.ing.baker.runtime.common.AsyncSupport.toAsync
import com.ing.baker.runtime.common.SyncSupport.syntax._
import com.ing.baker.runtime.common.{AsyncSupport, Fs2Support}
import com.ing.baker.il.{RecipeVisualStyle, RecipeVisualizer}
import com.ing.baker.runtime.common.BakerException.{ProcessAlreadyExistsException, ProcessDeletedException}
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, RecipeInstanceConfig}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult}
import fs2.{Pipe, Stream}

import scala.concurrent.duration.FiniteDuration
import java.util.concurrent.CompletableFuture
import java.util.concurrent.TimeoutException

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

  def fireEventStream(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Either[FireSensoryEventRejection, Stream[F, EventInstance]]] =
    fetch(recipeInstanceId).flatMap {
      case None =>
        async.pure(Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId)))
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        async.pure(Left(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId)))
      case Some(RecipeInstanceStatus.Active(recipeInstance, _)) =>
        recipeInstance.fireEventStream(event, correlationId)
    }

  def fireSensoryEventAndAwaitReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F], fs2Support: Fs2Support[F]): F[SensoryEventStatus] = {
    def awaitFirst(stream: Stream[F, EventInstance]): F[Unit] =
      oneShotSignal[Unit].flatMap { firstEventProcessed =>
        val signalingStream = stream.zipWithIndex.evalTap { case (_, index) =>
          if (index == 0) firstEventProcessed.complete(())
          else async.unit
        }.map(_._1)

        for {
          _ <- async.startAndForget(fs2Support.drain(signalingStream))
          _ <- firstEventProcessed.get
        } yield ()
      }

    fireEventStream(recipeInstanceId, event, correlationId)
      .flatMap(foldToStatus(awaitFirst))
  }

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F], fs2Support: Fs2Support[F]): F[SensoryEventStatus] =
    fireEventStream(recipeInstanceId, event, correlationId)
      .flatMap(foldToStatus(fs2Support.drain))

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F], fs2Support: Fs2Support[F]): F[SensoryEventResult] = {
    def awaitForCompletion(stream: Stream[F, EventInstance]): F[SensoryEventResult] =
      fs2Support.lastOrError(stream.through(aggregateResult))
    fireEventStream(recipeInstanceId, event, correlationId)
      .flatMap(foldToResult(awaitForCompletion))
  }

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F], fs2Support: Fs2Support[F]): F[SensoryEventResult] = {
    def awaitForEvent(stream: Stream[F, EventInstance]): F[SensoryEventResult] =
      oneShotSignal[SensoryEventResult].flatMap { eventDeferred =>
        fs2Support.drain(stream.through(aggregateResult).evalTap(intermediateResult =>
          if(intermediateResult.eventNames.contains(onEvent))
            eventDeferred.complete(intermediateResult)
          else async.unit
        )).flatMap(_ => eventDeferred.get)
      }
    fireEventStream(recipeInstanceId, event, correlationId)
      .flatMap(foldToResult(awaitForEvent))
  }

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F], fs2Support: Fs2Support[F]): F[(F[SensoryEventStatus], F[SensoryEventResult])] =
    fireEventStream(recipeInstanceId, event, correlationId)
      .flatMap(outcome =>
        for {
          received <- oneShotSignal[Unit]
          completed <- oneShotSignal[SensoryEventResult]
          _ <- outcome match {
            case Left(_) =>
              async.unit
            case Right(stream) =>
              fs2Support.drain(
                stream
                  .through(aggregateResult)
                  .last.evalTap(r => completed.complete(r.get))
              ).flatMap(_ => received.complete(()))
          }
        } yield (
          foldToStatus((_: Unit) => received.get)(outcome.map(_ => ())),
          foldToResult((_: Unit) => completed.get)(outcome.map(_ => ()))))

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

  def retryBlockedInteraction(recipeInstanceId: String, interactionName: String)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Stream[F, EventInstance]] =
    getExistent(recipeInstanceId).map(_.retryBlockedInteraction(interactionName))

  def resolveBlockedInteraction(recipeInstanceId: String, interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Stream[F, EventInstance]] =
    getExistent(recipeInstanceId).map(_.resolveBlockedInteraction(interactionName, eventInstance))

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

  private def aggregateResult: Pipe[F, EventInstance, SensoryEventResult] = {
    val zero = SensoryEventResult(SensoryEventStatus.Completed, Seq.empty, Map.empty)
    _.scan(zero)((result, event) =>
      result.copy(
        eventNames = result.eventNames :+ event.name,
        ingredients = result.ingredients ++ event.providedIngredients)
    )
  }

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