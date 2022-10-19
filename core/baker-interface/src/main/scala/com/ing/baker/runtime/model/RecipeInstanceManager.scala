package com.ing.baker.runtime.model

import cats.data.EitherT
import cats.effect.{ConcurrentEffect, Effect, Resource}
import cats.implicits._
import com.ing.baker.il.{RecipeVisualStyle, RecipeVisualizer}
import com.ing.baker.runtime.common.BakerException.{ProcessAlreadyExistsException, ProcessDeletedException}
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetaDataName
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult}
import com.ing.baker.types.MapType
import fs2.{Pipe, Stream}

import scala.concurrent.duration.{FiniteDuration, MILLISECONDS}
import scala.collection.immutable.Seq
import scala.jdk.CollectionConverters._
import cats.effect.{ Deferred, Temporal }

object RecipeInstanceManager {

  sealed trait RecipeInstanceStatus[F[_]]

  object RecipeInstanceStatus {

    case class Active[F[_]](recipeInstance: RecipeInstance[F]) extends RecipeInstanceStatus[F]

    case class Deleted[F[_]](recipeId: String, createdOn: Long, deletedOn: Long) extends RecipeInstanceStatus[F]
  }
}

trait RecipeInstanceManager[F[_]] {

  protected def store(newRecipeInstance: RecipeInstance[F])(implicit components: BakerComponents[F]): F[Unit]

  protected def fetch(recipeInstanceId: String): F[Option[RecipeInstanceStatus[F]]]

  protected def fetchAll: F[Map[String, RecipeInstanceStatus[F]]]

  protected def remove(recipeInstanceId: String): F[Unit]

  def idleStop(recipeInstanceId: String): F[Unit]

  def getAllRecipeInstancesMetadata: F[Set[RecipeInstanceMetadata]]

  def startRetentionPeriodStream(interval: FiniteDuration)(implicit effect: Effect[F], timer: Temporal[F]): Resource[F, Unit] =
    Stream.awakeEvery[F](interval).evalMap { _ =>
      for {
        allRecipeInstances <- fetchAll
        _ <- allRecipeInstances.toList.traverse { case (recipeInstanceId, instance) =>
          computeShouldDelete(instance).flatMap(shouldDelete =>
            if (shouldDelete) remove(recipeInstanceId) else effect.unit)
        }
      } yield ()
    }.compile.resource.drain

  def bake(recipeId: String, recipeInstanceId: String, config: RecipeInstance.Config)(implicit components: BakerComponents[F], effect: Effect[F], timer: Temporal[F]): F[Unit] =
    for {
      _ <- fetch(recipeInstanceId).flatMap[Unit] {
        case Some(RecipeInstanceStatus.Active(_)) =>
          effect.raiseError(ProcessAlreadyExistsException(recipeInstanceId))
        case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
          effect.raiseError(ProcessDeletedException(recipeInstanceId))
        case None =>
          effect.unit
      }
      recipeInfo <- components.recipeManager.getRecipe(recipeId)
      newRecipeInstance <- RecipeInstance.empty[F](recipeInfo.compiledRecipe, recipeInstanceId, config)
      _ <- store(newRecipeInstance)
    } yield ()

  def getRecipeInstanceState(recipeInstanceId: String)(implicit effect: Effect[F]): F[RecipeInstanceState] =
    getExistent(recipeInstanceId).flatMap(
      _.state.get.map { currentState =>
        RecipeInstanceState(
          recipeInstanceId,
          currentState.ingredients,
          currentState.events
        )
      })

  def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default)(implicit effect: Effect[F]): F[String] =
    for {
      recipeInstance <- getExistent(recipeInstanceId)
      currentState <- recipeInstance.state.get
    } yield RecipeVisualizer.visualizeRecipe(
      currentState.recipe,
      style,
      eventNames = currentState.events.map(_.name).toSet,
      ingredientNames = currentState.ingredients.keySet
    )

  def fireEventStream(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): EitherT[F, FireSensoryEventRejection, Stream[F, EventInstance]] =
    EitherT(fetch(recipeInstanceId).map {
      case None =>
        Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        Left(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId))
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
        Right(recipeInstance)
    }).flatMap(_.fireEventStream(event, correlationId))

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[SensoryEventStatus] =
    fireEventStream(recipeInstanceId, event, correlationId)
      .value.flatMap(foldToStatus(_.compile.drain))

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[SensoryEventResult] = {
    def awaitForCompletion(stream: Stream[F, EventInstance]): F[SensoryEventResult] =
      stream.through(aggregateResult).compile.lastOrError
    fireEventStream(recipeInstanceId, event, correlationId)
      .value.flatMap(foldToResult(awaitForCompletion))
  }

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[SensoryEventResult] = {
    def awaitForEvent(stream: Stream[F, EventInstance]): F[SensoryEventResult] =
      Deferred[F, SensoryEventResult].flatMap { eventDeferred =>
        stream.through(aggregateResult).evalTap(intermediateResult =>
          if(intermediateResult.eventNames.contains(onEvent))
            effect.attempt(eventDeferred.complete(intermediateResult)).void
          else effect.unit
        ).compile.drain *> eventDeferred.get
      }
    fireEventStream(recipeInstanceId, event, correlationId)
      .value.flatMap(foldToResult(awaitForEvent))
  }

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[(F[SensoryEventStatus], F[SensoryEventResult])] =
    fireEventStream(recipeInstanceId, event, correlationId)
      .value.flatMap(outcome =>
        for {
          received <- Deferred[F, Unit]
          completed <- Deferred[F, SensoryEventResult]
          _ <- outcome match {
            case Left(_) =>
              effect.unit
            case Right(stream) =>
              stream
                .through(aggregateResult)
                .last.evalTap(r => completed.complete(r.get))
                .compile.drain *> received.complete(())
          }
        } yield (
          foldToStatus((_: Unit) => received.get)(outcome.map(_ => ())),
          foldToResult((_: Unit) => completed.get)(outcome.map(_ => ()))))

  def addMetaData(recipeInstanceId: String, metadata: Map[String, String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[Unit] = {
    getExistent(recipeInstanceId).map((recipeInstance: RecipeInstance[F]) => {
      recipeInstance.state.update(currentState => {
        val newBakerMetaData = currentState.ingredients.get(RecipeInstanceMetaDataName) match {
          case Some(value) =>
            if (value.isInstanceOf(MapType(com.ing.baker.types.CharArray))) {
              val oldMetaData: Map[String, String] = value.asMap[String, String](classOf[String], classOf[String]).asScala.toMap
              oldMetaData ++ metadata
            }
            else metadata
          case None => metadata
        }
        currentState.copy(ingredients = currentState.ingredients + (RecipeInstanceMetaDataName -> com.ing.baker.types.Converters.toValue(newBakerMetaData)))
      })
    }).flatten
  }


  def stopRetryingInteraction(recipeInstanceId: String, interactionName: String)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[Unit] =
    getExistent(recipeInstanceId).flatMap(_.stopRetryingInteraction(interactionName))

  def retryBlockedInteraction(recipeInstanceId: String, interactionName: String)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[Stream[F, EventInstance]] =
    getExistent(recipeInstanceId).map(_.retryBlockedInteraction(interactionName))

  def resolveBlockedInteraction(recipeInstanceId: String, interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Temporal[F]): F[Stream[F, EventInstance]] =
    getExistent(recipeInstanceId).map(_.resolveBlockedInteraction(interactionName, eventInstance))

  private def getExistent(recipeInstanceId: String)(implicit effect: Effect[F]): F[RecipeInstance[F]] =
    fetch(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(recipeInstance)) => effect.pure(recipeInstance)
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) => effect.raiseError(BakerException.ProcessDeletedException(recipeInstanceId))
      case None => effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId))
    }

  private def aggregateResult: Pipe[F, EventInstance, SensoryEventResult] = {
    val zero = SensoryEventResult(SensoryEventStatus.Completed, Seq.empty, Map.empty)
    _.scan(zero)((result, event) =>
      result.copy(
        eventNames = result.eventNames :+ event.name,
        ingredients = result.ingredients ++ event.providedIngredients)
    )
  }

  private def foldToStatus[A](f: A => F[Unit])(outcome: Either[FireSensoryEventRejection, A])(implicit effect: Effect[F]): F[SensoryEventStatus] =
    outcome match {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        effect.raiseError(BakerException.IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        effect.pure(SensoryEventStatus.FiringLimitMet)
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        effect.pure(SensoryEventStatus.AlreadyReceived)
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        effect.pure(SensoryEventStatus.ReceivePeriodExpired)
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        effect.pure(SensoryEventStatus.RecipeInstanceDeleted)
      case Right(a) =>
        f(a).as(SensoryEventStatus.Received)
    }

  private def foldToResult[A](f: A => F[SensoryEventResult])(outcome: Either[FireSensoryEventRejection, A])(implicit effect: Effect[F]): F[SensoryEventResult] =
    outcome match {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        effect.raiseError(BakerException.IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(a) =>
        f(a)
    }

  private def computeShouldDelete(status: RecipeInstanceStatus[F])(implicit effect: Effect[F], timer: Temporal[F]): F[Boolean] =
    for {
      currentTime <- timer.clock.realTime(MILLISECONDS)
      result <- status match {
        case RecipeInstanceStatus.Active(recipeInstance) =>
          recipeInstance.state.get.map { currentState =>
            currentState.recipe.retentionPeriod.exists(_.toMillis + currentState.createdOn < currentTime)
          }
        case RecipeInstanceStatus.Deleted(_, _, _) =>
          effect.pure(false)
      }
    } yield result
}
