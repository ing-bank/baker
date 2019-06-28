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

  type SensoryEventMomentsType <: SensoryEventMoments[F] { type Language <: self.Language }

  type RuntimeEventType <: RuntimeEvent {type Language <: self.Language}

  type ProcessStateType <: ProcessState {type Language <: self.Language}

  type InteractionImplementationType <: InteractionImplementation[F] { type Language <: self.Language }

  type BakerEventType <: BakerEvent {type Language <: self.Language}

  type ProcessMetadataType <: ProcessMetadata {type Language <: self.Language}

  type RecipeInformationType <: RecipeInformation {type Language <: self.Language}

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  def addRecipe(compiledRecipe: CompiledRecipe): F[String]

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  def getRecipe(recipeId: String): F[RecipeInformationType]

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  def getAllRecipes: F[language.Map[String, RecipeInformationType]]

  /**
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @return
    */
  def bake(recipeId: String, processId: String): F[Unit]

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  def fireSensoryEventReceived(processId: String, event: RuntimeEventType): F[SensoryEventStatus]

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  def fireSensoryEventCompleted(processId: String, event: RuntimeEventType): F[SensoryEventResultType]

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  def fireSensoryEvent(processId: String, event: RuntimeEventType): SensoryEventMomentsType

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId     The process identifier
    * @param event         The event object
    * @param correlationId Id used to ensure the process instance handles unique events
    */
  def fireSensoryEventReceived(processId: String, event: RuntimeEventType, correlationId: String): F[SensoryEventStatus]

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId     The process identifier
    * @param event         The event object
    * @param correlationId Id used to ensure the process instance handles unique events
    */
  def fireSensoryEventCompleted(processId: String, event: RuntimeEventType, correlationId: String): F[SensoryEventResultType]

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId     The process identifier
    * @param event         The event object
    * @param correlationId Id used to ensure the process instance handles unique events
    */
  def fireSensoryEvent(processId: String, event: RuntimeEventType, correlationId: String): SensoryEventMomentsType

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId     The process identifier
    * @param event         The event object
    * @param correlationId Id used to ensure the process instance handles unique events
    */
  def fireSensoryEventReceived(processId: String, event: RuntimeEventType, correlationId: language.Option[String]): F[SensoryEventStatus]

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId     The process identifier
    * @param event         The event object
    * @param correlationId Id used to ensure the process instance handles unique events
    */
  def fireSensoryEventCompleted(processId: String, event: RuntimeEventType, correlationId: language.Option[String]): F[SensoryEventResultType]

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param processId     The process identifier
    * @param event         The event object
    * @param correlationId Id used to ensure the process instance handles unique events
    */
  def fireSensoryEvent(processId: String, event: RuntimeEventType, correlationId: language.Option[String]): SensoryEventMomentsType

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
  def getAllProcessesMetadata: F[language.Set[ProcessMetadataType]]

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  def getProcessState(processId: String): F[ProcessStateType]

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  def getIngredients(processId: String): F[language.Map[String, Value]]

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  def getVisualState(processId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): F[String]

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(recipeName: String, listenerFunction: language.BiConsumerFunction[String, RuntimeEventType]): F[Unit]

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listenerFunction: language.BiConsumerFunction[String, RuntimeEventType]): F[Unit]

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
    * Adds an interaction implementation to baker.
    *
    * @param implementation The implementation object
    */
  def addImplementation(implementation: InteractionImplementationType): F[Unit]

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  def addImplementations(implementations: language.Seq[InteractionImplementationType]): F[Unit]

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def gracefulShutdown(): F[Unit]

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  def retryInteraction(processId: String, interactionName: String): F[Unit]

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  def resolveInteraction(processId: String, interactionName: String, event: RuntimeEventType): F[Unit]

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  def stopRetryingInteraction(processId: String, interactionName: String): F[Unit]
}
