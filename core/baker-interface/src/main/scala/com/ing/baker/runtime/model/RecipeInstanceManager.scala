package com.ing.baker.runtime.model

import cats.Monad
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.model.RecipeInstanceManager.{BakeOutcome, GetRecipeInstanceStateOutcome, RecipeInstanceStatus}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.scaladsl.{EventMoment, RecipeInstanceState}

object RecipeInstanceManager {

  sealed trait BakeOutcome

  object BakeOutcome {

    case object Baked extends BakeOutcome

    case object RecipeInstanceDeleted extends BakeOutcome

    case object RecipeInstanceAlreadyExists extends BakeOutcome
  }

  sealed trait RecipeInstanceStatus

  object RecipeInstanceStatus {

    case class Active(recipeInstance: RecipeInstance, createdOn: Long) extends RecipeInstanceStatus

    case class Deleted(createdOn: Long, deletedOn: Long) extends RecipeInstanceStatus
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

  def bake(recipeInstanceId: String, recipe: CompiledRecipe)(implicit effect: Monad[F]): F[BakeOutcome] =
    getRecipeInstance(recipeInstanceId).flatMap {
      case Some(_: RecipeInstanceStatus.Active) =>
        effect.pure(BakeOutcome.RecipeInstanceAlreadyExists)
      case Some(_: RecipeInstanceStatus.Deleted) =>
        effect.pure(BakeOutcome.RecipeInstanceDeleted)
      case None =>
        addNewRecipeInstance(recipeInstanceId, recipe).as(BakeOutcome.Baked)
    }

  def getRecipeInstanceState(recipeInstanceId: String)(implicit effect: Monad[F]): F[GetRecipeInstanceStateOutcome] =
    getRecipeInstance(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(recipeInstance, _)) =>
        effect.pure(GetRecipeInstanceStateOutcome.Success(RecipeInstanceState(
          recipeInstanceId,
          recipeInstance.ingredients,
          recipeInstance.events.map { case (event, occurredOn) => EventMoment(event.name, occurredOn) }
        )))
      case Some(_: RecipeInstanceStatus.Deleted) =>
        effect.pure(GetRecipeInstanceStateOutcome.RecipeInstanceDeleted)
      case None =>
        effect.pure(GetRecipeInstanceStateOutcome.NoSuchRecipeInstance)
    }

  def getRecipeInstance(recipeInstanceId: String): F[Option[RecipeInstanceStatus]]

  def addNewRecipeInstance(recipeInstanceId: String, recipe: CompiledRecipe): F[Unit]

}
