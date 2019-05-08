package com.ing.baker.runtime.core

import com.ing.baker.il._
import com.ing.baker.types.Value

import scala.language.postfixOps

/**
  * The BakerInterface is a class we use to ensure the Scala and Java Baker classes have the same methods.
  *
  * @tparam F   the type of Future to use in the return types
  * @tparam Map the type of Map to use in the return types
  * @tparam Seq the type of Seq to use in the return types
  * @tparam Set the type of Set to use in the return types
  */
trait BakerInterface[F[_], Map[_, _], Seq[_], Set[_]] {

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
  def getAllRecipes: F[Map[String, RecipeInformation]]

  //TODO why does this return a processState? No new information will be in it.
  /**
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @return
    */
  def bake(recipeId: String, processId: String): F[Unit]

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  def processEvent(processId: String, event: Any): F[BakerResponse]

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  def processEvent(processId: String, event: Any, correlationId: String): F[BakerResponse]

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
  def getIndex(): F[Set[ProcessMetadata]]

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def getProcessState(processId: String): F[ProcessState]

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  def getIngredients(processId: String): F[Map[String, Value]]

  //TODO do we keep this a a future?
  //I think its strange this is a future from user perspective
  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the process state.
    * @return A visual (.dot) representation of the process state.
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getVisualState(processId: String): F[String]

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(recipeName: String, listener: EventListener): F[Unit]

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listener: EventListener): F[Unit]

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
  def addImplementations(implementations: Set[AnyRef]): F[Unit]

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
  def resolveInteraction(processId: String, interactionName: String, event: Any): F[Unit]

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  def stopRetryingInteraction(processId: String, interactionName: String): F[Unit]
}
