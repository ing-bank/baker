package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait BakerF[F[_]] extends common.Baker[F] with ScalaApi {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutionsF[F]

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstanceF[F]

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

}
