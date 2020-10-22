package com.ing.baker.runtime.inmemory

import cats.implicits._
import cats.effect.IO
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.model.{BakerComponents, RecipeInstanceManager}
import com.ing.baker.runtime.scaladsl.{BakerEvent, BakerF, EventInstance, EventMoment, EventResolutions, InteractionInstance, RecipeEventMetadata, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult}
import com.ing.baker.types.Value

final class InMemoryBaker(implicit components: BakerComponents[IO]) extends BakerF[IO] {

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe): IO[String] =
    components.recipeManager.addRecipe(compiledRecipe)

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): IO[RecipeInformation] =
    components.recipeManager.getRecipe(recipeId).flatMap {
      case Some((compiledRecipe, timestamp)) =>
        getImplementationErrors(compiledRecipe).map(
          RecipeInformation(compiledRecipe, timestamp, _))
      case None =>
        IO.raiseError(BakerException.NoSuchRecipeException(recipeId))
    }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: IO[Map[String, RecipeInformation]] =
    components.recipeManager.getAllRecipes.flatMap(_.toList
      .traverse { case (recipeId, (compiledRecipe, timestamp)) =>
        getImplementationErrors(compiledRecipe)
          .map(errors => recipeId -> RecipeInformation(compiledRecipe, timestamp, errors))
      }
      .map(_.toMap)
    )

  private def getImplementationErrors(compiledRecipe: CompiledRecipe): IO[Set[String]] = {
    //TODO optimize so that we do not have to much traffic if its a remote InteractionManager
    compiledRecipe.interactionTransitions.toList
      .traverse(x => components
        .interactionInstanceManager.contains(x)
        .map(has => (has, x.originalInteractionName)))
      .map(_
        .filterNot(_._1)
        .map(x => s"No implementation provided for interaction: ${x._2}")
        .toSet)
  }

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): IO[Unit] =
    for {
      recipeInfo <- getRecipe(recipeId)
      outcome <- components.recipeInstanceManager.bake(recipeInstanceId, recipeInfo.compiledRecipe)
      _ <- outcome match {
        case RecipeInstanceManager.BakeOutcome.Baked =>
          IO.unit
        case RecipeInstanceManager.BakeOutcome.RecipeInstanceDeleted =>
          IO.raiseError(BakerException.ProcessDeletedException(recipeInstanceId))
        case RecipeInstanceManager.BakeOutcome.RecipeInstanceAlreadyExists =>
          IO.raiseError(BakerException.ProcessAlreadyExistsException(recipeInstanceId))
      }
    } yield ()

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): IO[SensoryEventStatus] = ???

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): IO[SensoryEventResult] = ???

  /**
    * Notifies Baker that an event has happened and waits until an specific event has executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param onEvent          The name of the event to wait for
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): IO[SensoryEventResult] = ???

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = ???

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
  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] = ???

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): IO[RecipeInstanceState] = ???

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): IO[Map[String, Value]] = ???

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): IO[Seq[EventMoment]] = ???

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  override def getEventNames(recipeInstanceId: String): IO[Seq[String]] = ???

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): IO[String] = ???

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): IO[Unit] = ???

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): IO[Unit] = ???

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): IO[Unit] = ???

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation The implementation object
    */
  override def addInteractionInstance(implementation: InteractionInstance): IO[Unit] = ???

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addInteractionInstances(implementations: Seq[InteractionInstance]): IO[Unit] = ???

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): IO[Unit] = ???

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): IO[Unit] = ???

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): IO[Unit] = ???

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): IO[Unit] = ???
}
