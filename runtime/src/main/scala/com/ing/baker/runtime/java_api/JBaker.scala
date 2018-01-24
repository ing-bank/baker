package com.ing.baker.runtime.java_api

import java.util.concurrent.{TimeUnit, TimeoutException}
import java.util.{Collections, UUID}

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.processindex.ProcessMetadata
import com.ing.baker.runtime.core._
import com.ing.baker.types.Value

import scala.collection.JavaConverters._
import scala.concurrent.duration._

class JBaker(actorSystem: ActorSystem, implementations: java.lang.Iterable[AnyRef]) {
  private implicit class DurationConversions(timeout: java.time.Duration) {
    def toScala : FiniteDuration =
      FiniteDuration(timeout.toMillis, TimeUnit.MILLISECONDS)
  }

  addImplementations(implementations)

  def this(actorSystem: ActorSystem) = this(actorSystem, Collections.emptyList[AnyRef])

  def this() = this(ActorSystem("BakerActorSystem"))

  private val baker: Baker = new Baker()(actorSystem)

  def addRecipe(compiledRecipe: CompiledRecipe): String = baker.addRecipe(compiledRecipe)

  /**
    * Adds a single interaction implementation to baker.
    *
    * @param implementation The implementation that should be added.
    */
  def addImplementation(implementation: AnyRef): Unit = baker.addInteractionImplementation(implementation)

  /**
    * Adds all the provided interaction implementations to baker.
    *
    * @param implementations An iterable of implementations that should be added.
    */
  def addImplementations(implementations: java.lang.Iterable[AnyRef]) = implementations.asScala.foreach(addImplementation)

  /**
    * Attempts to gracefully shutdown the baker system.
    *
    * @param timeout The time to wait for the shard handover.
    */
  @throws[TimeoutException]("When the Baker does not shut down within the given deadline")
  def shutdown(timeout: java.time.Duration): Unit = baker.shutdown(Duration(timeout.toMillis, TimeUnit.MILLISECONDS))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  @throws[TimeoutException]("When the Baker does not shut down within the given deadline")
  def shutdown(): Unit = baker.shutdown()

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    */
  @throws[TimeoutException]("When the process is not baked within the given deadline")
  def bake(recipeId: String, processId: String): Unit =
    baker.bake(recipeId, processId)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    * @param timeout   the timeout for the Bake
    */
  @throws[TimeoutException]("When the process is not baked within the given deadline")
  def bake(recipeId: String, processId: String, timeout: java.time.Duration): Unit =
    baker.bake(recipeId, processId, timeout.toScala)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    */
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def bake(recipeId: String, processId: UUID): Unit = bake(recipeId, processId.toString)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    * @param timeout   the timeout for the Bake
    */
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def bake(recipeId: String, processId: UUID, timeout: java.time.Duration): Unit =
    bake(recipeId, processId.toString, timeout)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(processId: String, event: Any): Unit =
    baker.processEvent(processId, event)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(processId: String, event: Any, timeout: java.time.Duration): Unit =
    baker.processEvent(processId, event, timeout.toScala)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(processId: UUID, event: Any): Unit =
    processEvent(processId.toString, event)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(processId: UUID, event: Any, timeout: java.time.Duration): Unit =
    processEvent(processId.toString, event, timeout)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  def processEventAsync(processId: String, event: Any): BakerResponse = {
    implicit val executionContext = actorSystem.dispatcher
    baker.processEventAsync(processId, event)
  }

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  def processEventAsync(processId: String, event: Any, timeout: java.time.Duration): BakerResponse = {
    implicit val executionContext = actorSystem.dispatcher
    baker.processEventAsync(processId, event, timeout.toScala)
  }

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  def processEventAsync(processId: UUID, event: Any): BakerResponse =
    processEventAsync(processId.toString, event)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def processEventAsync(processId: UUID, event: Any, timeout: java.time.Duration): BakerResponse =
    processEventAsync(processId.toString, event, timeout)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId         The process identifier
    * @param timeout           the maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getIngredients(processId: String, timeout: java.time.Duration): java.util.Map[String, Value] =
    baker
      .getIngredients(processId, timeout.toScala)
      .asJava
      .asInstanceOf[java.util.Map[String, Value]]


  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId         The process identifier
    * @param timeout           The maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getIngredients(processId: UUID, timeout: java.time.Duration): java.util.Map[String, Value] =
    getIngredients(processId.toString, timeout)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(processId: String): java.util.Map[String, Value] =
    baker.getIngredients(processId).asJava

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
    * @param processId         The process identifier
    * @param timeout           The maximum wait time
    * @return
    *
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getEvents(processId: String, timeout: java.time.Duration): EventList =
    new EventList(baker.events(processId, timeout.toScala))

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId         The process identifier
    * @param timeout           The maximum wait time
    * @return
    *
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getEvents(processId: UUID, timeout: java.time.Duration): EventList =
    getEvents(processId.toString, timeout)

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
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getEvents(processId: String): EventList = getEvents(processId)

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getEvents(processId: UUID): EventList = getEvents(processId.toString)

  /**
    * Returns the compiled recipe for the given recipeId
    *
    * @param recipeId the recipeId
    * @return The compiled recipe
    */
  @throws[TimeoutException]("When the compiled recipe is not found within the default deadline")
  def getCompiledRecipe(recipeId: String): CompiledRecipe = baker.getRecipe(recipeId)

  /**
    * Returns the compiled recipe for the given recipeId
    *
    * @param recipeId the recipeId
    * @param timeout the maxium wait time
    * @return The compiled recipe
    */
  @throws[TimeoutException]("When the compiled recipe is not found within the given deadline")
  def getCompiledRecipe(recipeId: String, timeout: java.time.Duration): CompiledRecipe =
    baker.getRecipe(recipeId, timeout.toScala)

  /**
    * Return alls compiled recipes added to this Baker
    * @return A map with all recipes from recipeId -> CompiledRecipe
    */
  @throws[TimeoutException]("When the Baker does not respond within the default deadline")
  def getAllRecipes(): java.util.Map[String, CompiledRecipe] = baker.getAllRecipes().asJava

  /**
    * Return alls compiled recipes added to this Baker
    * @param timeout
    * @return A map with all recipes from recipeId -> CompiledRecipe
    */
  @throws[TimeoutException]("When the Baker does not respond within the given deadline")
  def getAllRecipes(timeout: java.time.Duration): java.util.Map[String, CompiledRecipe] =
    baker.getAllRecipes(timeout.toScala).asJava

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
    * @param recipeName the name of all recipes this event listener should be triggered for
    * @param listener   The listener to subscribe to events.
    */
  def registerEventListener(recipeName: String, listener: EventListener): Unit = baker.registerEventListener(recipeName, listener)

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
    * @param processId         The process identifier
    * @param timeout           The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: String, timeout: java.time.Duration): String =
    baker.getVisualState(processId, timeout.toScala)

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId         The process identifier
    * @param timeout           The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: UUID, timeout: java.time.Duration): String =
    getVisualState(processId, timeout)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: String): String =
    getVisualState(processId)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(processId: UUID): String =
    getVisualState(processId.toString)

  def getAllProcessMetadata: java.util.Set[ProcessMetadata] =
    baker.allProcessMetadata.asJava
}
