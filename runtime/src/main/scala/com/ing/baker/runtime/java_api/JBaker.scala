package com.ing.baker.runtime.java_api

import java.util.UUID
import java.util.concurrent.{TimeUnit, TimeoutException}

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.ProcessMetadata
import com.ing.baker.runtime.core._
import com.ing.baker.runtime.petrinet.ReflectedInteractionTask

import scala.collection.JavaConverters._
import scala.concurrent.duration._

class JBaker (compiledRecipe: CompiledRecipe,
              implementations: java.util.List[AnyRef],
              actorSystem: ActorSystem) {

  def this(compiledRecipe: CompiledRecipe, implementations: java.util.List[AnyRef]) =
    this(compiledRecipe, implementations, ActorSystem("BakerActorSystem"))

  val baker: Baker = new Baker(
    compiledRecipe = compiledRecipe,
    implementations = ReflectedInteractionTask.implementationsToProviderMap(implementations.asScala))(actorSystem = actorSystem)

  val defaultTimeout: Int = 20 * 1000
  val defaultHandleEventAsyncTimeout: FiniteDuration = FiniteDuration.apply(10, TimeUnit.SECONDS)

  /**
    * Attempts to gracefully shutdown the baker system.
    *
    * @param timeout The time to wait for the shard handover.
    */
  def shutdown(timeout: java.time.Duration): Unit = baker.shutdown(Duration(timeout.toMillis, TimeUnit.MILLISECONDS))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def shutdown(): Unit = baker.shutdown()

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param processId The process identifier
    */
  def bake(processId: String): Unit =
    baker.bake(processId)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param processId The process identifier
    */
  def bake(processId: UUID): Unit =
    this.bake(processId.toString)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def processEvent(processId: String, event: Any): Unit =
    processEventAsync(processId, event).confirmCompleted()

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def processEvent(processId: UUID, event: Any): Unit =
    this.processEvent(processId.toString, event)


  /**
    * Processes an event and awaits confirms the firing of a specific event.
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @param eventName The name of the event to confirm.
    */
  def processEventAndConfirmEvent(processId: String, event: Any, eventName: String): SensoryEventStatus =
    baker.handleEventAndConfirmEvent(processId, event, eventName)(defaultHandleEventAsyncTimeout)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def processEventAsync(processId: String, event: Any): BakerResponse = {
    implicit val executionContext = actorSystem.dispatcher
    baker.handleEventAsync(processId, event)(defaultHandleEventAsyncTimeout)
  }

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event The event to fire
    * @return
    */
  def processEventAsync(processId: UUID, event: Any): BakerResponse =
    this.processEventAsync(processId.toString, event)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis the maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String, waitTimeoutMillis: Long): java.util.Map[String, Object] =
    baker
      .getIngredients(processId)(waitTimeoutMillis milliseconds)
      .asJava
      .asInstanceOf[java.util.Map[String, Object]]


  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis the maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: UUID, waitTimeoutMillis: Long): java.util.Map[String, Object] =
    getIngredients(processId.toString, waitTimeoutMillis)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the default deadline")
  def getIngredients(processId: String): java.util.Map[String, Object] =
    getIngredients(processId, defaultTimeout)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the default deadline")
  def getIngredients(processId: UUID): java.util.Map[String, Object] =
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
    new EventList(baker.events(processId)(waitTimeoutMillis milliseconds))

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
  def getEvents(processId: UUID, waitTimeoutMillis: Long): EventList =
    getEvents(processId.toString, waitTimeoutMillis)

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
  def getEvents(processId: String): EventList =
    getEvents(processId, defaultTimeout)

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @return
    */
  def getEvents(processId: UUID): EventList =
    getEvents(processId.toString, defaultTimeout)

  /**
    * Returns the compiled recipe.
    *
    * @return The compiled recipe
    */
  def getCompiledRecipe: CompiledRecipe = compiledRecipe

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
  def registerEventListener(listener: EventListener): Unit = baker.registerEventListener(listener)

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the default deadline")
  def getVisualState(processId: String, waitTimeoutMillis: Long): String =
    baker.getVisualState(processId)(waitTimeoutMillis milliseconds)

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId The process identifier
    * @param waitTimeoutMillis The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the default deadline")
  def getVisualState(processId: UUID, waitTimeoutMillis: Long): String =
    getVisualState(processId, waitTimeoutMillis)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  def getVisualState(processId: String): String =
    getVisualState(processId, defaultTimeout)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  def getVisualState(processId: UUID): String =
    getVisualState(processId.toString)

  def getAllProcessMetadata: java.util.Set[ProcessMetadata] =
    baker.allProcessMetadata.asJava
}
