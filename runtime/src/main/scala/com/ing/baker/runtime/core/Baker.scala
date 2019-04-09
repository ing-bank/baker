package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.stream.scaladsl.Source
import com.ing.baker.il._
import com.ing.baker.runtime.core.events.BakerEvent
import com.ing.baker.types.{Converters, RecordValue, Value}

import scala.concurrent.Future
import scala.concurrent.duration.FiniteDuration
import scala.language.postfixOps

object Baker {

  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def extractEvent(event: Any): RuntimeEvent = {
    // transforms the given object into a RuntimeEvent instance
    event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case obj                        =>
        Converters.toValue(obj) match {
          case RecordValue(entries) => RuntimeEvent(obj.getClass.getSimpleName, entries.toSeq)
          case other                => throw new IllegalArgumentException(s"Unexpected value: $other")
        }
    }
  }
}

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker {

  val defaultBakeTimeout: FiniteDuration
  val defaultProcessEventTimeout: FiniteDuration
  val defaultInquireTimeout: FiniteDuration
  val defaultShutdownTimeout: FiniteDuration
  val defaultAddRecipeTimeout: FiniteDuration

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def addRecipe(compiledRecipe: CompiledRecipe, timeout: FiniteDuration = defaultAddRecipeTimeout): String

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getRecipe(recipeId: String, timeout: FiniteDuration = defaultInquireTimeout): RecipeInformation

  /**
    * Returns the compiled recipe for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getCompiledRecipe(recipeId: String, timeout: FiniteDuration = defaultInquireTimeout): CompiledRecipe

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getAllRecipes(timeout: FiniteDuration = defaultInquireTimeout): Map[String, RecipeInformation]

  /**
    * Returns a future of all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  def getAllRecipesAsync(timeout: FiniteDuration = defaultInquireTimeout): Future[Map[String, RecipeInformation]]
  /**
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def bake(recipeId: String, processId: String, timeout: FiniteDuration = defaultBakeTimeout): ProcessState

  /**
    * Asynchronously creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  def bakeAsync(recipeId: String, processId: String, timeout: FiniteDuration = defaultBakeTimeout): Future[ProcessState]

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def processEvent(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): SensoryEventStatus

  /**
    * Notifies Baker that an event has happened.
    *
    * If nothing is done with the BakerResponse there is NO guarantee that the event is received by the process instance.
    */
  def processEventAsync(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): BakerResponse

  /**gf
    * Retries a blocked interaction.
    *
    * @return
    */
  def retryInteraction(processId: String, interactionName: String, timeout: FiniteDuration = defaultProcessEventTimeout): Unit

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  def resolveInteraction(processId: String, interactionName: String, event: Any, timeout: FiniteDuration = defaultProcessEventTimeout): Unit

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  def stopRetryingInteraction(processId: String, interactionName: String, timeout: FiniteDuration = defaultProcessEventTimeout): Unit

  /**
    * Synchronously returns all event names that occurred for a process.
    */
  def eventNames(processId: String, timeout: FiniteDuration = defaultInquireTimeout): List[String]

  /**
    * Returns a stream of all events with their timestamps for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsWithTimestampAsync(processId: String): Source[(RuntimeEvent, Long), NotUsed]

  /**
    * Returns a stream of all events for a process.
    *
    * @param processId The process identifier.
    * @return A sequence of events with their timestamps.
    */
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed]

  /**
    * Synchronously returns a sequence of all events for a process.
    *
    * @param processId The process identifier.
    * @param timeout How long to wait to retrieve the events.
    */
  def events(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Seq[RuntimeEvent]

  /**
    * Synchronously returns a sequence of all events with their timestamps for a process.
    *
    * @param processId The process identifier.
    * @param timeout How long to wait to retrieve the events.
    * @return A sequence of events with their timestamps.
    */
  def eventsWithTimestamp(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Seq[(RuntimeEvent, Long)]

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
  def getIndex(timeout: FiniteDuration = defaultInquireTimeout): Set[ProcessMetadata]

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getProcessState(processId: String, timeout: FiniteDuration = defaultInquireTimeout): ProcessState
  /**
    * returns a future with the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getProcessStateAsync(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Future[ProcessState]

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Map[String, Value]

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  def getIngredientsAsync(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Future[Map[String, Value]]

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the process state.
    * @return A visual (.dot) representation of the process state.
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getVisualState(processId: String, timeout: FiniteDuration = defaultInquireTimeout): String

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(recipeName: String, listener: EventListener): Boolean

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
//  @deprecated("Use event bus instead", "1.4.0")
  def registerEventListener(listener: EventListener): Boolean
  /**
    * This registers a listener function.
    *
    * @param pf A partial function that receives the events.
    * @return
    */
  def registerEventListenerPF(pf: PartialFunction[BakerEvent, Unit]): Boolean

  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  def addImplementation(implementation: AnyRef): Unit
  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  def addImplementations(implementations: Seq[AnyRef]): Unit

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  def addImplementation(implementation: InteractionImplementation): Unit

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def gracefulShutdown(timeout: FiniteDuration = defaultShutdownTimeout): Unit
}
