package com.ing.baker.runtime.scaladsl

import cats.~>
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.types.Value

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait BakerF[F[_]] extends common.Baker[F] with ScalaApi { self =>

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

  def translate[G[_]](mapK: F ~> G, comapK: G ~> F): BakerF[G] =
    new BakerF[G] {
      override def addRecipe(compiledRecipe: CompiledRecipe): G[String] =
        mapK(self.addRecipe(compiledRecipe))
      override def getRecipe(recipeId: String): G[RecipeInformation] =
        mapK(self.getRecipe(recipeId))
      override def getAllRecipes: G[Map[String, RecipeInformation]] =
        mapK(self.getAllRecipes)
      override def bake(recipeId: String, recipeInstanceId: String): G[Unit] =
        mapK(self.bake(recipeId, recipeInstanceId))
      override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): G[SensoryEventStatus] =
        mapK(self.fireEventAndResolveWhenReceived(recipeInstanceId, event, correlationId))
      override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): G[SensoryEventResult] =
        mapK(self.fireEventAndResolveWhenCompleted(recipeInstanceId, event, correlationId))
      override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): G[SensoryEventResult] =
        mapK(self.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, correlationId))
      override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutionsF[G] =
        self.fireEvent(recipeInstanceId, event, correlationId).translate(mapK)
      override def getAllRecipeInstancesMetadata: G[Set[RecipeInstanceMetadata]] =
        mapK(self.getAllRecipeInstancesMetadata)
      override def getRecipeInstanceState(recipeInstanceId: String): G[RecipeInstanceState] =
        mapK(self.getRecipeInstanceState(recipeInstanceId))
      override def getIngredients(recipeInstanceId: String): G[Map[String, Value]] =
        mapK(self.getIngredients(recipeInstanceId))
      override def getEvents(recipeInstanceId: String): G[Seq[EventMoment]] =
        mapK(self.getEvents(recipeInstanceId))
      override def getEventNames(recipeInstanceId: String): G[Seq[String]] =
        mapK(self.getEventNames(recipeInstanceId))
      override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): G[String] =
        mapK(self.getVisualState(recipeInstanceId))
      override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): G[Unit] =
        mapK(self.registerEventListener(recipeName, listenerFunction))
      override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): G[Unit] =
        mapK(self.registerEventListener(listenerFunction))
      override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): G[Unit] =
        mapK(self.registerBakerEventListener(listenerFunction))
      override def addInteractionInstance(implementation: InteractionInstanceF[G]): G[Unit] =
        mapK(self.addInteractionInstance(implementation.translate(comapK)))
      override def addInteractionInstances(implementations: Seq[InteractionInstanceF[G]]): G[Unit] =
        mapK(self.addInteractionInstances(implementations.map(_.translate(comapK))))
      override def gracefulShutdown(): G[Unit] =
        mapK(self.gracefulShutdown())
      override def retryInteraction(recipeInstanceId: String, interactionName: String): G[Unit] =
        mapK(self.retryInteraction(recipeInstanceId, interactionName))
      override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): G[Unit] =
        mapK(self.resolveInteraction(recipeInstanceId, interactionName, event))
      override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): G[Unit] =
        mapK(self.stopRetryingInteraction(recipeInstanceId, interactionName))
    }
}
