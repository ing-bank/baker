package com.ing.baker.runtime.model

import cats.data.EitherT
import cats.{Functor, Monad}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.{RejectReason, SensoryEventStatus}
import com.ing.baker.runtime.model.RecipeInstanceManager.{BakeOutcome, FireOutcome, FireSensoryEventRejection, GetRecipeInstanceStateOutcome, RecipeInstanceStatus}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FireTransitionValidation
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment, EventResolutionsF, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult}

object RecipeInstanceManager {

  type FireOutcome[F[_], A] = EitherT[F, FireSensoryEventRejection, A]

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
    get(recipeInstanceId).flatMap {
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
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

  def add(recipeInstanceId: String, recipe: CompiledRecipe): F[Unit]

  def get(recipeInstanceId: String): F[Option[RecipeInstanceStatus]]

  def getAllRecipeInstancesMetadata: F[Set[RecipeInstanceMetadata]]

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F]): FireOutcome[F, SensoryEventStatus]

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F]): FireOutcome[F, SensoryEventResult]

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String])(implicit components: BakerComponents[F]): FireOutcome[F, SensoryEventResult]

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F]): (FireOutcome[F, SensoryEventStatus], FireOutcome[F, SensoryEventResult])

  protected def getRecipeInstanceWithRejection(recipeInstanceId: String)(implicit effect: Functor[F]): FireOutcome[F, RecipeInstance] =
    EitherT(get(recipeInstanceId).map {
      case None =>
        Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
      case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
        Left(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId))
      case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
        Right(recipeInstance)
    })

}
