package com.ing.baker.runtime.common

import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

/**
  * The BakerInterface is a class we use to ensure the Scala and Java Baker classes have the same methods.
  *
  * @tparam F the type of Future to use in the return types
  */
trait Baker[F[_]] extends LanguageApi {
  self =>

  type SensoryEventResultType <: SensoryEventResult {type Language <: self.Language}

  type EventResolutionsType <: EventResolutions[F] {type Language <: self.Language}

  type EventInstanceType <: EventInstance {type Language <: self.Language}

  type RecipeInstanceStateType <: RecipeInstanceState {type Language <: self.Language}

  type InteractionInstanceType <: InteractionInstance[F] {type Language <: self.Language}

  type InteractionInstanceDescriptorType <: InteractionInstanceDescriptor {type Language <: self.Language}

  type IngredientInstanceType <: IngredientInstance { type Language <: self.Language }

  type BakerEventType <: BakerEvent {type Language <: self.Language}

  type RecipeInstanceMetadataType <: RecipeInstanceMetadata {type Language <: self.Language}

  type RecipeInformationType <: RecipeInformation {type Language <: self.Language}

  type EventMomentType <: EventMoment { type Language <: self.Language}

  type RecipeMetadataType <: RecipeEventMetadata { type Language <: self.Language }

  type InteractionExecutionResultType <: InteractionExecutionResult { type Language <: self.Language }

  type DurationType

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  def addRecipe(compiledRecipe: CompiledRecipe, timeCreated: Long, validate: Boolean): F[String] = addRecipe(RecipeRecord.of(compiledRecipe, updated = timeCreated, validate = validate))

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  def addRecipe(compiledRecipe: CompiledRecipe, validate: Boolean): F[String] = addRecipe(compiledRecipe, System.currentTimeMillis(), validate)

  /**
    * Adds recipe as a record
    * @param recipe
    * @return
    */
  def addRecipe(recipe: RecipeRecord): F[String]

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  def getRecipe(recipeId: String): F[RecipeInformationType]

  def getRecipeVisual(recipeId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): F[String]

  /**
    * Returns all 'active' recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  def getAllRecipes: F[language.Map[String, RecipeInformationType]]

  def getAllInteractions: F[language.Seq[InteractionInstanceDescriptorType]]

  def getInteraction(interactionName: String): F[language.Option[InteractionInstanceDescriptorType]]

  def executeSingleInteraction(interactionId : String, ingredients : language.Seq[IngredientInstanceType]): F[InteractionExecutionResultType]

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  def bake(recipeId: String, recipeInstanceId: String): F[Unit]


  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    * This variant also gets a metadata map added on bake.
    * This is similar to calling addMetaData after doing the regular bake but depending on the implementation this can be more optimized.
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @param metadata
    * @return
    */
  def bake(recipeId: String, recipeInstanceId: String, metadata: language.Map[String, String]): F[Unit]

  /**
   * Deletes a recipeInstance. Once deleted the instance will be marked as `Deleted` in the index and then removed after a while.
   * Use `removeFromIndex` to remove all references to the instance directly allowing you to create a new instance with the same id again.
   * @param recipeInstanceId The identifier for the newly baked process
   * @param removeFromIndex If enabled removes all references to the id directly
   * @return
   */
  def deleteRecipeInstance(recipeInstanceId: String, removeFromIndex: Boolean): F[Unit]

  /**
   * Fires a sensory event for a given recipe instance and waits until it has been accepted and persisted.
   *
   * This method is fast and returns as soon as the event is stored in the journal. It does NOT wait for
   * any interactions to be executed.
   *
   * @param recipeInstanceId The identifier of the recipe instance.
   * @param event            The sensory event instance to fire.
   * @param correlationId    An optional correlation identifier. If provided, Baker guarantees that an event with the
   *                         same correlation ID is only processed once. This is crucial for building idempotent
   *                         systems. If a second event with the same ID arrives, the method will fail with
   *                         [[AlreadyReceivedException]].
   * @return A future that resolves to [[SensoryEventStatus.Received]] when the event has been successfully persisted.
   * @throws NoSuchProcessException                if the recipe instance does not exist.
   * @throws ProcessDeletedException               if the recipe instance has been deleted.
   * @throws InvalidEventException                 if the event is not a valid sensory event for the recipe.
   * @throws AlreadyReceivedException              if an event with the same `correlationId` has already been received.
   * @throws java.util.concurrent.TimeoutException if the request does not complete within the configured `baker.process-event-timeout`.
   *                                               Note that a timeout does NOT mean the event was not processed; it may still be
   *                                               processed later.
   */
  def fireSensoryEventAndAwaitReceived(recipeInstanceId: String, event: EventInstanceType, correlationId: language.Option[String]): F[SensoryEventStatus]

  /**
   * Waits for a specific event to be fired and persisted for a recipe instance.
   *
   * This method polls the event history of the recipe instance until an event with the given name appears,
   * or until the specified timeout is reached.
   *
   * If the provided `eventName` is not defined in the recipe, this method will fail immediately with
   * [[InvalidEventException]].
   *
   * @param recipeInstanceId The identifier of the recipe instance.
   * @param eventName        The name of the event to wait for. This can be any event, not just a sensory one.
   * @param timeout          The maximum duration to wait for the event.
   * @return A future that resolves to [[SensoryEventStatus.Completed]] when the event is found.
   * @throws InvalidEventException   if the `eventName` is not defined in the recipe. This check is performed upfront.
   * @throws NoSuchProcessException  if the recipe instance does not exist.
   * @throws ProcessDeletedException if the recipe instance has been deleted.
   * @throws TimeoutException        if the event does not occur within the specified `timeout`.
   */
  def awaitEvent(recipeInstanceId: String, eventName: String, timeout: DurationType, waitForNext: Boolean = false): F[Unit]

  /**
   * Waits until a recipe instance completes execution.
   *
   * An execution is considered completed when there are no more running or scheduled jobs (e.g., interactions, delayed events).
   * This is useful for ensuring that a process has fully completed its execution flow after an event has been fired.
   *
   * @param recipeInstanceId The identifier of the recipe instance.
   * @param timeout          The maximum duration to wait for the execution to become completed.
   * @return A future that resolves to [[SensoryEventStatus.Completed]] when the executions has completed.
   * @throws NoSuchProcessException  if the recipe instance does not exist.
   * @throws ProcessDeletedException if the recipe instance has been deleted.
   * @throws TimeoutException        if the execution does not complete within the specified `timeout`.
   */
  def awaitCompleted(recipeInstanceId: String, timeout: DurationType): F[SensoryEventStatus]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstanceType): F[SensoryEventStatus]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstanceType): F[SensoryEventResultType]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstanceType, on: String): F[SensoryEventResultType]

  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  def fireEvent(recipeInstanceId: String, event: EventInstanceType): EventResolutionsType

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstanceType, correlationId: String): F[SensoryEventStatus]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstanceType, correlationId: String): F[SensoryEventResultType]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstanceType, onEvent: String, correlationId: String): F[SensoryEventResultType]

  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  def fireEvent(recipeInstanceId: String, event: EventInstanceType, correlationId: String): EventResolutionsType

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.", "5.1.0")
  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstanceType, correlationId: language.Option[String]): F[SensoryEventStatus]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.", "5.1.0")
  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstanceType, correlationId: language.Option[String]): F[SensoryEventResultType]

  @deprecated("This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.", "5.1.0")
  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstanceType, onEvent: String, correlationId: language.Option[String]): F[SensoryEventResultType]

  @deprecated("This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.", "5.1.0")
  def fireEvent(recipeInstanceId: String, event: EventInstanceType, correlationId: language.Option[String]): EventResolutionsType

  /**
    * This method is used to add metadata to your request. This will be added to the ingredients map in Baker.
    * Since this is meant to be used as metadata this should not
    * These cannot be ingredients already found in your recipe.
    * @param metadata
    */
  def addMetaData(recipeInstanceId: String, metadata: language.Map[String, String]): F[Unit]

  /**
    * Returns an index of all running processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the given timeout.
    *
    * Does not include deleted processes.
    *
    * @return An index of all processes
    */
  def getAllRecipeInstancesMetadata: F[language.Set[RecipeInstanceMetadataType]]

  /**
   * Check if recipe instance exists and is active.
   *
   * @param recipeInstanceId The recipe instance identifier
   * @return true if recipe instance exists, and is in active state, otherwise false.
   */
  def hasRecipeInstance(recipeInstanceId: String): F[Boolean]

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  def getRecipeInstanceState(recipeInstanceId: String): F[RecipeInstanceStateType]

  /**
    * Returns a specific ingredient for a given RecipeInstance id.
    *
    * @param recipeInstanceId The recipeInstance Id.
    * @param name The name of the ingredient.
    * @return The provided ingredients.
    */
  def getIngredient(recipeInstanceId: String, name: String): F[Value]

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  def getIngredients(recipeInstanceId: String): F[language.Map[String, Value]]

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  def getEvents(recipeInstanceId: String): F[language.Seq[EventMomentType]]

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  def getEventNames(recipeInstanceId: String): F[language.Seq[String]]

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): F[String]

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(recipeName: String, listenerFunction: language.BiConsumerFunction[RecipeMetadataType, String]): F[Unit]

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listenerFunction: language.BiConsumerFunction[RecipeMetadataType, String]): F[Unit]

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  def registerBakerEventListener(listenerFunction: language.ConsumerFunction[BakerEventType]): F[Unit]

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def gracefulShutdown(): F[Unit]

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  def retryInteraction(recipeInstanceId: String, interactionName: String): F[Unit]

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstanceType): F[Unit]

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): F[Unit]
}

case class RecipeRecord(
                         recipeId: String,
                         name: String,
                         updated: Long,
                         recipe: CompiledRecipe,
                         validate: Boolean,
                         isActive: Boolean = true
                       )
object RecipeRecord {
  def of(recipe: CompiledRecipe, updated: Long = System.currentTimeMillis(), validate: Boolean = true, isActive: Boolean = true) =
    RecipeRecord(recipe.recipeId, recipe.name, updated, recipe, validate, isActive)
}
