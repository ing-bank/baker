package com.ing.baker.runtime.javadsl

import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.common.{RecipeRecord, SensoryEventStatus}
import com.ing.baker.runtime.common
import com.ing.baker.types.Value

import java.time.Duration
import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture
import java.util.function.{BiConsumer, Consumer}
import javax.annotation.Nonnull
import scala.annotation.nowarn

trait BakerCommon extends common.Baker[CompletableFuture] with JavaApi with AutoCloseable {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type InteractionInstanceDescriptorType = InteractionInstanceDescriptor

  override type IngredientInstanceType = IngredientInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override type RecipeMetadataType = RecipeEventMetadata

  override type InteractionExecutionResultType = InteractionExecutionResult

  override type DurationType = Duration

  override type UnitType = Void

  /**
   * Adds a recipe to baker and returns a recipeId for the recipe.
   *
   * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId.
   *
   * @param recipeRecord The RecipeRecord recipe.
   * @return A recipe identifier.
   */
  def addRecipe(@Nonnull recipeRecord: RecipeRecord): CompletableFuture[String]

  /**
   * Adds a recipe to baker and returns a recipeId for the recipe.
   *
   * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
   *
   * @param compiledRecipe The compiled recipe.
   * @return A recipeId
   */
  override def addRecipe(compiledRecipe: CompiledRecipe, timeCreated: Long, validate: Boolean): CompletableFuture[String] =
    addRecipe(RecipeRecord.of(compiledRecipe, updated = timeCreated, validate = validate))

  /**
   * Adds a recipe to baker and returns a recipeId for the recipe.
   *
   * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
   *
   * @param compiledRecipe The compiled recipe.
   * @return A recipeId
   */
  override def addRecipe(compiledRecipe: CompiledRecipe, validate: Boolean): CompletableFuture[String] =
    addRecipe(compiledRecipe, System.currentTimeMillis(), validate)

  /**
   * Attempts to gracefully shutdown the baker system.
   */
  def gracefulShutdown(): CompletableFuture[UnitType]

  /**
   * This bakes (creates) a new process instance of the recipe.
   *
   * @param recipeId         The recipe this instance will be baked for
   * @param recipeInstanceId The process identifier
   */
  def bake(@Nonnull recipeId: String, @Nonnull recipeInstanceId: String): CompletableFuture[UnitType]

  /**
   * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
   * This variant also gets a metadata map added on bake.
   * This is similar to calling addMetaData after doing the regular bake but depending on the implementation this can be more optimized.
   *
   * @param recipeId         The recipeId for the recipe to bake
   * @param recipeInstanceId The identifier for the newly baked process
   * @param metadata         Metadata
   * @return
   */
  def bake(recipeId: String, recipeInstanceId: String, metadata: util.Map[String, String]): CompletableFuture[UnitType]

  def deleteRecipeInstance(recipeInstanceId: String, removeFromIndex: Boolean): CompletableFuture[UnitType]

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  def fireEventAndResolveWhenReceived(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: String): CompletableFuture[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.of(correlationId))

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  def fireEventAndResolveWhenCompleted(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.of(correlationId))

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  def fireEventAndResolveOnEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull onEvent: String, @Nonnull correlationId: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.of(correlationId))

  @Deprecated
  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  def fireEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: String): EventResolutions =
    fireEvent(recipeInstanceId, event, Optional.of(correlationId))

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  def fireEventAndResolveWhenReceived(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance): CompletableFuture[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.empty[String]())

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  def fireEventAndResolveWhenCompleted(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.empty[String]())

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  def fireEventAndResolveOnEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull onEvent: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.empty[String]())

  @Deprecated
  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  def fireEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance): EventResolutions =
    fireEvent(recipeInstanceId, event, Optional.empty[String]())

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  def fireEventAndResolveWhenReceived(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: Optional[String]): CompletableFuture[SensoryEventStatus]

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  @nowarn
  def fireEventAndResolveWhenCompleted(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: Optional[String]): CompletableFuture[SensoryEventResult]

  @Deprecated
  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  @nowarn
  def fireEventAndResolveOnEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull onEvent: String, @Nonnull correlationId: Optional[String]): CompletableFuture[SensoryEventResult]

  @Deprecated
  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  @nowarn
  def fireEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: Optional[String]): EventResolutions

  /**
   * Retries a blocked interaction.
   *
   * @param recipeInstanceId The process identifier.
   * @param interactionName  The name of the blocked interaction.
   * @return
   */
  def retryInteraction(@Nonnull recipeInstanceId: String, @Nonnull interactionName: String): CompletableFuture[UnitType]

  /**
   * Resolves a blocked interaction by giving it's output.
   *
   * @param recipeInstanceId The process identifier.
   * @param interactionName  The name of the blocked interaction.
   * @param event            The output of the interaction.
   * @return
   */
  def resolveInteraction(@Nonnull recipeInstanceId: String, @Nonnull interactionName: String, @Nonnull event: EventInstance): CompletableFuture[UnitType]

  /**
   * Stops a retrying interaction.
   *
   * @param recipeInstanceId The process identifier.
   * @param interactionName  The name of the retrying interaction.
   * @return
   */
  def stopRetryingInteraction(@Nonnull recipeInstanceId: String, @Nonnull interactionName: String): CompletableFuture[UnitType]

  /**
   * Check if recipe instance exists and is active.
   *
   * @param recipeInstanceId The recipe instance identifier
   * @return true if recipe instance exists, and is in active state, otherwise false.
   */
  def hasRecipeInstance(recipeInstanceId: String): CompletableFuture[Boolean]

  /**
   * Returns the state of a process instance. This includes the ingredients and names of the events.
   *
   * @param recipeInstanceId The process identifier
   * @return The state of the process instance
   */
  def getRecipeInstanceState(@Nonnull recipeInstanceId: String): CompletableFuture[RecipeInstanceState]

  /**
   * @param recipeInstanceId The recipeInstance Id.
   * @param name             The name of the ingredient.
   * @return The provided ingredients.
   */
  def getIngredient(recipeInstanceId: String, name: String): CompletableFuture[Value]

  /**
   * Returns all the ingredients that are accumulated for a given process.
   *
   * @param recipeInstanceId The process identifier
   * @return
   */
  def getIngredients(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.Map[String, Value]]

  /**
   * Returns all fired events for a given RecipeInstance id.
   *
   * @param recipeInstanceId The process id.
   * @return The events
   */
  @nowarn
  def getEvents(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.List[EventMoment]]

  /**
   * Returns all names of fired events for a given RecipeInstance id.
   *
   * @param recipeInstanceId The process id.
   * @return The event names
   */
  @nowarn
  def getEventNames(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.List[String]]

  /**
   * Returns the recipe information for the given RecipeId
   *
   * @param recipeId the recipeId
   * @return The JRecipeInformation recipe
   */
  def getRecipe(@Nonnull recipeId: String): CompletableFuture[RecipeInformation]

  def getRecipeVisual(recipeId: String, style: RecipeVisualStyle): CompletableFuture[String]

  /**
   * Return alls 'active' recipes added to this Baker
   *
   * @return A map with all recipes from recipeId -> JRecipeInformation
   */
  @nowarn
  def getAllRecipes: CompletableFuture[java.util.Map[String, RecipeInformation]]

  @nowarn
  def getInteraction(interactionName: String): CompletableFuture[Optional[InteractionInstanceDescriptorType]]

  @nowarn
  def getAllInteractions: CompletableFuture[java.util.List[InteractionInstanceDescriptorType]]

  @nowarn
  def executeSingleInteraction(interactionId: String, ingredients: util.List[IngredientInstanceType]): CompletableFuture[InteractionExecutionResult]

  /**
   * Returns an index of all processes.
   *
   * Can potentially return a partial index when baker runs in cluster mode
   * and not all shards can be reached within the given timeout.
   *
   * Does not include deleted processes.
   *
   * @return An index of all processes
   */
  @nowarn
  def getAllRecipeInstancesMetadata: CompletableFuture[util.Set[RecipeInstanceMetadata]]

  /**
   * Registers a listener to all runtime events for this baker instance.
   *
   * Note that:
   *
   * - The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
   * - The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.
   *
   * Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:
   *
   * - logging
   * - metrics
   * - unit tests
   * - ...
   *
   * @param recipeName       the name of all recipes this event listener should be triggered for
   * @param listenerFunction The listener to subscribe to events.
   */
  override def registerEventListener(@Nonnull recipeName: String, @Nonnull listenerFunction: BiConsumer[RecipeEventMetadata, String]): CompletableFuture[UnitType]

  /**
   * Registers a listener function to all runtime events for this baker instance.
   *
   * Note that:
   *
   * - The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
   * - The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.
   *
   * Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:
   *
   * - logging
   * - metrics
   * - unit tests
   * - ...
   *
   * @param listenerFunction The listener function that is called once these events occur
   */
  override def registerEventListener(@Nonnull listenerFunction: BiConsumer[RecipeEventMetadata, String]): CompletableFuture[UnitType]

  /**
   * Registers a listener function to all runtime events for this baker instance.
   *
   * Note that:
   *
   * - The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
   * - The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.
   *
   * Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:
   *
   * - logging
   * - metrics
   * - unit tests
   * - ...
   *
   * @param eventListener The EventListener class the processEvent will be called once these events occur
   */
  @Deprecated
  @deprecated(message = "Replaced with the consumer function variant", since = "3.0.0")
  def registerEventListener(@Nonnull eventListener: EventListener): CompletableFuture[UnitType]

  /**
   * Registers a listener that listens to all Baker events
   *
   * @param listenerFunction
   * @return
   */
  override def registerBakerEventListener(@Nonnull listenerFunction: Consumer[BakerEvent]): CompletableFuture[UnitType]

  /**
   * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
   *
   * @param recipeInstanceId The process identifier
   * @return
   */
  def getVisualState(@Nonnull recipeInstanceId: String): CompletableFuture[String] =
    getVisualState(recipeInstanceId, RecipeVisualStyle.default)

  /**
   * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
   *
   * @param recipeInstanceId The process identifier
   * @return
   */
  def getVisualState(@Nonnull recipeInstanceId: String, @Nonnull style: RecipeVisualStyle): CompletableFuture[String]

  /**
   * This method is used to add metadata to your request. This will be added to the ingredients map in Baker.
   * Since this is meant to be used as metadata this should not
   * These cannot be ingredients already found in your recipe.
   *
   * @param metadata
   */
  override def addMetaData(recipeInstanceId: String, metadata: java.util.Map[String, String]): CompletableFuture[UnitType]

  def fireSensoryEventAndAwaitReceived(recipeInstanceId: String, event: EventInstance): CompletableFuture[SensoryEventStatus] =
    fireSensoryEventAndAwaitReceived(recipeInstanceId, event, Optional.empty())

  override def fireSensoryEventAndAwaitReceived(recipeInstanceId: String, event: EventInstance, correlationId: Optional[String]): CompletableFuture[SensoryEventStatus]

  /**
   * Convenience overload for Java callers that don't want to specify waitForNext.
   */
  def awaitEvent(recipeInstanceId: String, eventName: String, timeout: Duration): CompletableFuture[UnitType] =
    awaitEvent(recipeInstanceId, eventName, timeout, waitForNext = false)

  override def awaitEvent(recipeInstanceId: String, eventName: String, timeout: Duration, waitForNext: Boolean): CompletableFuture[UnitType]

  override def awaitCompleted(recipeInstanceId: String, timeout: Duration): CompletableFuture[SensoryEventStatus]
}
