package com.ing.baker.runtime.model

import cats.effect.{ConcurrentEffect, ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, NoSuchRecipeException, ProcessAlreadyExistsException}
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.{RejectReason, SensoryEventStatus}
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.scaladsl._

class Baker

/* This is going great, except `EventResolutions` and `Interactioninstance` should be parametriced on the effect type F[_], now are set to Future, this has some implications

abstract class Baker[F[_]](recipeManager: RecipeManager[F],
                           interactionManager: InteractionManager[F],
                           recipeInstanceManager: RecipeInstanceManager[F])
                          (implicit timer: Timer[F], eff: ConcurrentEffect[F]) extends common.Baker[F] with ScalaApi {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override type RecipeMetadataType = RecipeEventMetadata

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance): F[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, None)

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): F[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, None)

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String): F[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, None)

  override def fireEvent(recipeInstanceId: String, event: EventInstance): EventResolutionsType =
    fireEvent(recipeInstanceId, event, None)

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: String): F[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Some(correlationId))

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: String): F[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Some(correlationId))

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: String): F[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Some(correlationId))

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String): EventResolutionsType =
    fireEvent(recipeInstanceId, event, Some(correlationId))

  override def addRecipe(compiledRecipe: CompiledRecipe): F[String] =
    recipeManager.addRecipe(compiledRecipe)

  override def getRecipe(recipeId: String): F[RecipeInformation] =
    recipeManager.getRecipe(recipeId).flatMap {
      case Right(a) => eff.pure(a)
      case Left(e) => eff.raiseError(e)
    }

  override def getAllRecipes: F[Map[String, RecipeInformation]] =
    recipeManager.getAllRecipes

  override def addInteractionInstance(implementation: InteractionInstance): F[Unit] =
    interactionManager.addImplementation(implementation)

  override def bake(recipeId: String, recipeInstanceId: String): F[Unit] =
    recipeInstanceManager.bake(recipeId, recipeInstanceId).flatMap {
      case RecipeInstanceManager.BakeOutcome.Baked =>
        eff.unit
      case RecipeInstanceManager.BakeOutcome.RecipeInstanceDeleted =>
        eff.raiseError(ProcessAlreadyExistsException(recipeInstanceId))
      case RecipeInstanceManager.BakeOutcome.RecipeInstanceAlreadyExists =>
        eff.raiseError(NoSuchRecipeException(recipeId))
    }

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[SensoryEventStatus] =
    recipeInstanceManager.fireEventAndResoleWhenReceived(recipeInstanceId, event, correlationId).flatMap {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        eff.raiseError(IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        eff.raiseError(NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        eff.pure(SensoryEventStatus.FiringLimitMet)
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        eff.pure(SensoryEventStatus.AlreadyReceived)
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        eff.pure(SensoryEventStatus.ReceivePeriodExpired)
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        eff.pure(SensoryEventStatus.RecipeInstanceDeleted)
      case Right(status) =>
        eff.pure(status)
    }

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[SensoryEventResult] =
    recipeInstanceManager.fireEventAndResoleWhenCompleted(recipeInstanceId, event, correlationId, waitForRetries = true).flatMap {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        eff.raiseError(IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        eff.raiseError(NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(result) =>
        eff.pure(result)
    }

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstanceType, onEvent: String, correlationId: Option[String]): F[SensoryEventResult] =
    recipeInstanceManager.fireEventAndResolveOnEvent(recipeInstanceId, event, correlationId, waitForRetries = true, onEvent).flatMap {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        eff.raiseError(IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        eff.raiseError(NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(result) =>
        eff.pure(result)
    }

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = ???



  /*
  processIndexActor.ask(ProcessEvent(
    recipeInstanceId = recipeInstanceId,
    event = event,
    correlationId = correlationId,
    timeout = config.timeouts.defaultProcessEventTimeout,
    reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
  ))(config.timeouts.defaultProcessEventTimeout).flatMap {
    case FireSensoryEventRejection.InvalidEvent(_, message) =>
      F.failed(IllegalEventException(message))
    case FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0) =>
      F.raiseError(NoSuchProcessException(recipeInstanceId0))
    case _: FireSensoryEventRejection.FiringLimitMet =>
      Future.successful(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.AlreadyReceived =>
      Future.successful(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.ReceivePeriodExpired =>
      Future.successful(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.RecipeInstanceDeleted =>
      Future.successful(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
    case ProcessEventCompletedResponse(result) =>
      Future.successful(result)
  }
   */
}
 */
