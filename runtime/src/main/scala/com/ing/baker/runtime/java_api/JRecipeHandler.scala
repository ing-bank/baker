package com.ing.baker.runtime.java_api

import java.util.UUID
import java.util.concurrent.{TimeUnit, TimeoutException}

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.ProcessMetadata
import com.ing.baker.runtime.core.{BakerResponse, EventListener, NoSuchProcessException, RecipeHandler}
import com.ing.baker.types.Value

import scala.collection.JavaConverters._
import scala.concurrent.duration._

class JRecipeHandler(recipeHandler: RecipeHandler)(implicit val actorSystem: ActorSystem) {

  val defaultTimeout: Int = 20 * 1000

  val defaultHandleEventAsyncTimeout: FiniteDuration = FiniteDuration.apply(10, TimeUnit.SECONDS)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param processId The process identifier
    */
  def bake(processId: String): Unit = recipeHandler.bake(processId)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param processId The process identifier
    */
  def bake(processId: UUID): Unit = bake(processId.toString)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def handleEvent(processId: String, event: Any): Unit = handleEventAsync(processId, event).confirmCompleted()

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def handleEvent(processId: UUID, event: Any): Unit = handleEvent(processId.toString, event)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def handleEventAsync(processId: String, event: Any): BakerResponse = {
    implicit val executionContext = actorSystem.dispatcher
    recipeHandler.handleEventAsync(processId, event)(defaultHandleEventAsyncTimeout)
  }

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def handleEventAsync(processId: UUID, event: Any): BakerResponse =
    handleEventAsync(processId.toString, event)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis the maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(processId: String, waitTimeoutMillis: Long): java.util.Map[String, Value] =
    recipeHandler
      .getIngredients(processId)(waitTimeoutMillis milliseconds)
      .asJava
      .asInstanceOf[java.util.Map[String, Value]]


  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis the maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(processId: UUID, waitTimeoutMillis: Long): java.util.Map[String, Value] =
    getIngredients(processId.toString, waitTimeoutMillis)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(processId: String): java.util.Map[String, Value] =
    getIngredients(processId, defaultTimeout)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(processId: UUID): java.util.Map[String, Value] =
    getIngredients(processId.toString)

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis The maximum wait time
    * @return
    *
    */
  def getEvents(processId: String, waitTimeoutMillis: Long): EventList =
    new EventList(recipeHandler.events(processId)(waitTimeoutMillis milliseconds))

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis The maximum wait time
    * @return
    *
    */
  def getEvents(processId: UUID, waitTimeoutMillis: Long): EventList = getEvents(processId.toString, waitTimeoutMillis)

  /**
    * Returns all events that have occurred for a given process.
    *
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @return
    */
  def getEvents(processId: String): EventList = getEvents(processId, defaultTimeout)

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @return
    */
  def getEvents(processId: UUID): EventList = getEvents(processId.toString, defaultTimeout)

  /**
    * Returns the compiled recipe.
    *
    * @return The compiled recipe
    */
  def getCompiledRecipe: CompiledRecipe = recipeHandler.compiledRecipe

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
    * @param listener The listener to subscribe to events.
    */
  def registerEventListener(listener: EventListener): Unit = recipeHandler.registerEventListener(listener)

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: String, waitTimeoutMillis: Long): String =
    recipeHandler.getVisualState(processId)(waitTimeoutMillis milliseconds)

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: UUID, waitTimeoutMillis: Long): String = getVisualState(processId, waitTimeoutMillis)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: String): String = getVisualState(processId, defaultTimeout)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  def getVisualState(processId: UUID): String = getVisualState(processId.toString)

  def getAllProcessMetadata: java.util.Set[ProcessMetadata] = recipeHandler.allProcessMetadata.asJava
}
