package com.ing.baker.runtime.model

import cats.data.{EitherT, OptionT}
import cats.effect.{ConcurrentEffect, Sync, Timer}
import cats.implicits._
import cats.{Functor, Monad}
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle, RecipeVisualizer}
import com.ing.baker.runtime.common.{BakerException, RejectReason}
import com.ing.baker.runtime.model.RecipeInstanceManager.{BakeOutcome, FireSensoryEventRejection, GetRecipeInstanceStateOutcome, RecipeInstanceStatus}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.model.recipeinstance.execution.EventsLobby
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceMetadata, RecipeInstanceState}

object RecipeInstanceManager {

  sealed trait BakeOutcome

  // TODO Remove this and fail immediately in the manager operations with BakerExceptions
  object BakeOutcome {

    case object Baked extends BakeOutcome

    case object RecipeInstanceDeleted extends BakeOutcome

    case object RecipeInstanceAlreadyExists extends BakeOutcome
  }

  sealed trait RecipeInstanceStatus[F[_]]

  // TODO Remove this and fail immediately in the manager operations with BakerExceptions
  object RecipeInstanceStatus {

    case class Active[F[_]](recipeInstance: RecipeInstance[F]) extends RecipeInstanceStatus[F]

    case class Deleted[F[_]](recipeId: String, createdOn: Long, deletedOn: Long) extends RecipeInstanceStatus[F]
  }

  sealed trait GetRecipeInstanceStateOutcome

  // TODO Remove this and fail immediately in the manager operations with BakerExceptions
  object GetRecipeInstanceStateOutcome {

    case class Success(state: RecipeInstanceState) extends GetRecipeInstanceStateOutcome

    case object RecipeInstanceDeleted extends GetRecipeInstanceStateOutcome

    case object NoSuchRecipeInstance extends GetRecipeInstanceStateOutcome
  }

  sealed trait FireSensoryEventRejection {

    def asReason: RejectReason
  }

  object FireSensoryEventRejection {

    /**
      * Indicates that a process can no longer receive events because the configured period has expired.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class ReceivePeriodExpired(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ReceivePeriodExpired
    }

    /**
      * @param msg error message for the request
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class InvalidEvent(recipeInstanceId: String, msg: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.InvalidEvent
    }

    /**
      * Returned if a process has been deleted
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class RecipeInstanceDeleted(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ProcessDeleted
    }

    /**
      * Returned if the process is uninitialized
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class NoSuchRecipeInstance(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.NoSuchProcess
    }

    /**
      * The firing limit, the number of times this event may fire, was met.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class FiringLimitMet(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.FiringLimitMet
    }

    /**
      * An event with the same correlation id was already received.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      * @param correlationId The identifier used to secure uniqueness
      */
    case class AlreadyReceived(recipeInstanceId: String, correlationId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.AlreadyReceived
    }
  }
}

trait RecipeInstanceManager[F[_]] {

  def add(recipeInstanceId: String, recipe: CompiledRecipe): F[Unit]

  def get(recipeInstanceId: String): F[Option[RecipeInstanceStatus[F]]]

  def update(recipeInstanceId: String, updateFunction: RecipeInstance[F] => RecipeInstance[F]): F[RecipeInstance[F]]

  def idleStop(recipeInstanceId: String): F[Unit]

  def getAllRecipeInstancesMetadata: F[Set[RecipeInstanceMetadata]]

  def getExistent(recipeInstanceId: String)(implicit effect: Sync[F]): F[RecipeInstance[F]] =
    get(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(recipeInstance)) => effect.pure(recipeInstance)
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) => effect.raiseError(BakerException.ProcessDeletedException(recipeInstanceId))
      case None => effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId))
    }

  // TODO have to fail directly, see if getExistent matches the exeptions on the Baker level
  def bake(recipeInstanceId: String, recipe: CompiledRecipe)(implicit effect: Monad[F]): F[BakeOutcome] =
    get(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(_)) =>
        effect.pure(BakeOutcome.RecipeInstanceAlreadyExists)
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        effect.pure(BakeOutcome.RecipeInstanceDeleted)
      case None =>
        add(recipeInstanceId, recipe).as(BakeOutcome.Baked)
    }

  // TODO same as last one
  def getRecipeInstanceState(recipeInstanceId: String)(implicit effect: Monad[F]): F[GetRecipeInstanceStateOutcome] =
    get(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
        recipeInstance.state.get.map { currentState =>
          GetRecipeInstanceStateOutcome.Success(RecipeInstanceState(
            recipeInstanceId,
            currentState.ingredients,
            currentState.events
          ))
        }
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        effect.pure(GetRecipeInstanceStateOutcome.RecipeInstanceDeleted)
      case None =>
        effect.pure(GetRecipeInstanceStateOutcome.NoSuchRecipeInstance)
    }

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, EventsLobby[F]] =
    for {
      recipeInstance <- getRecipeInstanceWithPossibleRejection(recipeInstanceId)
      eventsLobby <- recipeInstance.fire(event, correlationId)
    } yield eventsLobby

  def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default)(implicit effect: Sync[F]): F[String] =
    for {
      recipeInstance <- getExistent(recipeInstanceId)
      currentState <- recipeInstance.state.get
    } yield RecipeVisualizer.visualizeRecipe(
      recipeInstance.recipe,
      style,
      eventNames = currentState.events.map(_.name).toSet,
      ingredientNames = currentState.ingredients.keySet
    )

  def stopRetryingInteraction(recipeInstanceId: String, interactionName: String)(implicit effect: ConcurrentEffect[F]): F[Unit] =
    for {
      recipeInstance <- getExistent(recipeInstanceId)
      _ <- recipeInstance.stopRetryingInteraction(interactionName)
    } yield ()

  def retryBlockedInteraction(recipeInstanceId: String, interactionName: String)(implicit effect: ConcurrentEffect[F]): F[Unit] =
    for {
      recipeInstance <- getExistent(recipeInstanceId)
      _ <- recipeInstance.retryBlockedInteraction(interactionName)
    } yield ()

  def resolveBlockedInteraction(recipeInstanceId: String, interactionName: String, eventInstance: EventInstance)(implicit effect: ConcurrentEffect[F], timer: Timer[F]): F[Unit] =
    for {
      recipeInstance <- getExistent(recipeInstanceId)
      _ <- recipeInstance.resolveBlockedInteraction(interactionName, eventInstance)
    } yield ()

  // TODO same as last 2
  private def getRecipeInstanceWithPossibleRejection(recipeInstanceId: String)(implicit effect: Functor[F]): EitherT[F, FireSensoryEventRejection, RecipeInstance[F]] =
    EitherT(get(recipeInstanceId).map {
      case None =>
        Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        Left(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId))
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
        Right(recipeInstance)
    })

}
