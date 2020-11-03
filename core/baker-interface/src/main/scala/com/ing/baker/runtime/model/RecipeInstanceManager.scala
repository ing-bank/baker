package com.ing.baker.runtime.model

import cats.data.EitherT
import cats.effect.{Timer, ConcurrentEffect}
import cats.implicits._
import cats.{Functor, Monad}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.model.RecipeInstanceManager.{BakeOutcome, FireSensoryEventRejection, GetRecipeInstanceStateOutcome, RecipeInstanceStatus}
import com.ing.baker.runtime.model.recipeinstance.{EventsLobby, RecipeInstance}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceMetadata, RecipeInstanceState}

object RecipeInstanceManager {

  sealed trait BakeOutcome

  object BakeOutcome {

    case object Baked extends BakeOutcome

    case object RecipeInstanceDeleted extends BakeOutcome

    case object RecipeInstanceAlreadyExists extends BakeOutcome
  }

  sealed trait RecipeInstanceStatus

  object RecipeInstanceStatus {

    case class Active(recipeInstance: RecipeInstance) extends RecipeInstanceStatus

    case class Deleted(recipeId: String, createdOn: Long, deletedOn: Long) extends RecipeInstanceStatus
  }

  sealed trait GetRecipeInstanceStateOutcome

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

  def get(recipeInstanceId: String): F[Option[RecipeInstanceStatus]]

  def update(recipeInstanceId: String, updateFunction: RecipeInstance => RecipeInstance): F[RecipeInstance]

  def getAllRecipeInstancesMetadata: F[Set[RecipeInstanceMetadata]]

  def bake(recipeInstanceId: String, recipe: CompiledRecipe)(implicit effect: Monad[F]): F[BakeOutcome] =
    get(recipeInstanceId).flatMap {
      case Some(_: RecipeInstanceStatus.Active) =>
        effect.pure(BakeOutcome.RecipeInstanceAlreadyExists)
      case Some(_: RecipeInstanceStatus.Deleted) =>
        effect.pure(BakeOutcome.RecipeInstanceDeleted)
      case None =>
        add(recipeInstanceId, recipe).as(BakeOutcome.Baked)
    }

  def getRecipeInstanceState(recipeInstanceId: String)(implicit effect: Monad[F]): F[GetRecipeInstanceStateOutcome] =
    get(recipeInstanceId).map {
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
        GetRecipeInstanceStateOutcome.Success(RecipeInstanceState(
          recipeInstanceId,
          recipeInstance.ingredients,
          recipeInstance.events
        ))
      case Some(_: RecipeInstanceStatus.Deleted) =>
        GetRecipeInstanceStateOutcome.RecipeInstanceDeleted
      case None =>
        GetRecipeInstanceStateOutcome.NoSuchRecipeInstance
    }

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, EventsLobby[F]] =
    for {
      recipeInstance <- getRecipeInstanceWithPossibleRejection(recipeInstanceId)
      lobby <- EitherT.liftF(EventsLobby.build[F])
      runEffect <- recipeInstance.fire[F](event, correlationId)(lobby, update)
      _ <- EitherT.liftF(runEffect)
    } yield lobby

  private def getRecipeInstanceWithPossibleRejection(recipeInstanceId: String)(implicit effect: Functor[F]): EitherT[F, FireSensoryEventRejection, RecipeInstance] =
    EitherT(get(recipeInstanceId).map {
      case None =>
        Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        Left(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId))
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
        Right(recipeInstance)
    })

}
