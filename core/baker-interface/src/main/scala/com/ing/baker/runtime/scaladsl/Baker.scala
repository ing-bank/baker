package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus

import scala.concurrent.Future
import scala.concurrent.duration.FiniteDuration

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker extends common.Baker[Future] with ScalaApi {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type InteractionInstanceDescriptorType =  InteractionInstanceDescriptor

  override type IngredientInstanceType = IngredientInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override type RecipeMetadataType = RecipeEventMetadata

  override type InteractionExecutionResultType = InteractionExecutionResult

  override type DurationType = FiniteDuration

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance): Future[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, None)

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): Future[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, None)

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String): Future[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, None)

  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  override def fireEvent(recipeInstanceId: String, event: EventInstance): EventResolutionsType =
    fireEvent(recipeInstanceId, event, None)

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: String): Future[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Some(correlationId))

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: String): Future[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Some(correlationId))

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: String): Future[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Some(correlationId))

  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String): EventResolutionsType =
    fireEvent(recipeInstanceId, event, Some(correlationId))

  def fireSensoryEventAndAwaitReceived(recipeInstanceId: String, event: EventInstance): Future[SensoryEventStatus] =
    fireSensoryEventAndAwaitReceived(recipeInstanceId, event, Option.empty)

}
