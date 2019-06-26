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

  type Result <: SensoryEventResult {type Language <: self.Language}

  // TODO rename it... Stages? Outcomes? Instances? Instants? Results?
  type Moments <: SensoryEventMoments[F] {type Language <: self.Language}

  type Event <: RuntimeEvent {type Language <: self.Language}

  type PState <: ProcessState {type Language <: self.Language}

  type BakerEventType <: BakerEvent {type Language <: self.Language}

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
  def getRecipe(recipeId: String): F[RecipeInformation]

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  def getAllRecipes: F[language.Map[String, RecipeInformation]]

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
  def fireSensoryEventReceived(processId: String, event: Event): F[SensoryEventStatus]

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
  def fireSensoryEventCompleted(processId: String, event: Event): F[Result]

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
  def fireSensoryEvent(processId: String, event: Event): Moments

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
  def fireSensoryEventReceived(processId: String, event: Event, correlationId: String): F[SensoryEventStatus]

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
  def fireSensoryEventCompleted(processId: String, event: Event, correlationId: String): F[Result]

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
  def fireSensoryEvent(processId: String, event: Event, correlationId: String): Moments

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
  def fireSensoryEventReceived(processId: String, event: Event, correlationId: language.Option[String]): F[SensoryEventStatus]

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
  def fireSensoryEventCompleted(processId: String, event: Event, correlationId: language.Option[String]): F[Result]

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
  def fireSensoryEvent(processId: String, event: Event, correlationId: language.Option[String]): Moments

  //TODO why do we have this and do we want to keep this?
  //TODO why is this named index when it return ProcessMetaData?
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
  def getIndex: F[language.Set[ProcessMetadata]]

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  def getProcessState(processId: String): F[PState]

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
  def registerEventListener(recipeName: String, listenerFunction: language.BiConsumerFunction[String, Event]): F[Unit]

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listenerFunction: language.BiConsumerFunction[String, Event]): F[Unit]

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listener
    * @return
    */
  //TODO split the BakerEvent also between java and scala interface.
  def registerBakerEventListener(listenerFunction: language.ConsumerFunction[BakerEventType]): F[Unit]

  //TODO remove AnyRef as a valid implementation.
  //Provide a helper method to go from AnyRef to InteractionImplementation
  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  def addImplementation(implementation: AnyRef): F[Unit]

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  def addImplementations(implementations: language.Seq[AnyRef]): F[Unit]

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  def addImplementation(implementation: InteractionImplementation): F[Unit]

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
  def resolveInteraction(processId: String, interactionName: String, event: Event): F[Unit]

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  def stopRetryingInteraction(processId: String, interactionName: String): F[Unit]
}
