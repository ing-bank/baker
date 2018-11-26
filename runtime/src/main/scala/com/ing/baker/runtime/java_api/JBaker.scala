package com.ing.baker.runtime.java_api

import java.util.concurrent.{TimeUnit, TimeoutException}
import java.util.{Collections, UUID}

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.core._
import com.ing.baker.runtime.core.events.AnnotatedEventSubscriber
import com.ing.baker.types.Value
import javax.annotation.Nonnull

import scala.collection.JavaConverters._
import scala.concurrent.duration._

class JBaker(private val baker: Baker, implementations: java.lang.Iterable[AnyRef]) {

  def this(actorSystem: ActorSystem, implementations: java.lang.Iterable[AnyRef]) = this(new Baker()(actorSystem), implementations)

  def this(actorSystem: ActorSystem) = this(actorSystem, Collections.emptyList[AnyRef])

  def this() = this(ActorSystem("BakerActorSystem"))

  addImplementations(implementations)

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId.
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipe identifier.
    */
  def addRecipe(@Nonnull compiledRecipe: CompiledRecipe): String = baker.addRecipe(compiledRecipe)

  /**
    * Adds a single interaction implementation to baker.
    *
    * @param implementation The implementation that should be added.
    */
  def addImplementation(@Nonnull implementation: AnyRef): Unit = baker.addImplementation(implementation)

  /**
    * Adds all the provided interaction implementations to baker.
    *
    * @param implementations An iterable of implementations that should be added.
    */
  def addImplementations(@Nonnull implementations: java.lang.Iterable[AnyRef]): Unit = implementations.asScala.foreach(addImplementation)

  /**
    * Attempts to gracefully shutdown the baker system.
    *
    * @param timeout The time to wait for the shard handover.
    */
  @throws[TimeoutException]("When the Baker does not shut down within the given deadline")
  def gracefulShutdown(timeout: java.time.Duration): Unit = baker.gracefulShutdown(Duration(timeout.toMillis, TimeUnit.MILLISECONDS))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  @throws[TimeoutException]("When the Baker does not shut down within the given deadline")
  def gracefulShutdown(): Unit = baker.gracefulShutdown()

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    */
  @throws[TimeoutException]("When the process is not baked within the given deadline")
  def bake(@Nonnull recipeId: String, @Nonnull processId: String): Unit =
    baker.bake(recipeId, processId)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    * @param timeout   the timeout for the Bake
    */
  @throws[TimeoutException]("When the process is not baked within the given deadline")
  def bake(@Nonnull recipeId: String, @Nonnull processId: String, @Nonnull timeout: java.time.Duration): Unit =
    baker.bake(recipeId, processId, timeout.toScala)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    */
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def bake(@Nonnull recipeId: String, @Nonnull processId: UUID): Unit = bake(recipeId, processId.toString)

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    * @param timeout   the timeout for the Bake
    */
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def bake(@Nonnull recipeId: String, @Nonnull processId: UUID, @Nonnull timeout: java.time.Duration): Unit =
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
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: String, @Nonnull event: Any): SensoryEventStatus =
    baker.processEvent(processId, event, None)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: UUID, @Nonnull event: Any): SensoryEventStatus =
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
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: String, @Nonnull event: Any, @Nonnull timeout: java.time.Duration): SensoryEventStatus =
    baker.processEvent(processId, event, None, timeout.toScala)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: UUID, @Nonnull event: Any, @Nonnull timeout: java.time.Duration): SensoryEventStatus =
    processEvent(processId.toString, event, timeout)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: String, @Nonnull event: Any, @Nonnull correlationId: String): SensoryEventStatus =
    baker.processEvent(processId, event, Some(correlationId))

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: UUID, @Nonnull event: Any, @Nonnull correlationId: String): SensoryEventStatus =
    processEvent(processId.toString, event, correlationId)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @param timeout       How long to wait for a response from the process
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: String, @Nonnull event: Any, @Nonnull correlationId: String, @Nonnull timeout: java.time.Duration): SensoryEventStatus =
    baker.processEvent(processId, event, Some(correlationId), timeout.toScala)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @param timeout       How long to wait for a response from the process
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def processEvent(@Nonnull processId: UUID, @Nonnull event: Any, @Nonnull correlationId: String, @Nonnull timeout: java.time.Duration): SensoryEventStatus =
    processEvent(processId.toString, event, correlationId, timeout)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  def processEventAsync(@Nonnull processId: String, @Nonnull event: Any): BakerResponse =
    baker.processEventAsync(processId, event)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @return
    */
  def processEventAsync(@Nonnull processId: UUID, @Nonnull event: Any): BakerResponse =
    processEventAsync(processId.toString, event)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @param timeout   How long to wait for a response from the process
    * @return
    */
  def processEventAsync(@Nonnull processId: String, @Nonnull event: Any, @Nonnull timeout: java.time.Duration): BakerResponse =
    baker.processEventAsync(processId, event, None, timeout.toScala)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId The process identifier
    * @param event     The event to fire
    * @param timeout   How long to wait for a response from the process
    * @return
    */
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def processEventAsync(@Nonnull processId: UUID, @Nonnull event: Any, @Nonnull timeout: java.time.Duration): BakerResponse =
    processEventAsync(processId.toString, event, timeout)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @return
    */
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def processEventAsync(@Nonnull processId: String, @Nonnull event: Any, @Nonnull correlationId: String): BakerResponse =
    baker.processEventAsync(processId, event, Some(correlationId))

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @return
    */
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def processEventAsync(@Nonnull processId: UUID, @Nonnull event: Any, @Nonnull correlationId: String): BakerResponse =
    baker.processEventAsync(processId.toString, event, Some(correlationId))

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @param timeout       How long to wait for a response from the process
    * @return
    */
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def processEventAsync(@Nonnull processId: String, @Nonnull event: Any, @Nonnull correlationId: String, @Nonnull timeout: java.time.Duration): BakerResponse =
    baker.processEventAsync(processId, event, Some(correlationId), timeout.toScala)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a BakerResponse.
    *
    * @param processId     The process identifier
    * @param event         The event to fire
    * @param correlationId An identifier for the event
    * @param timeout       How long to wait for a response from the process
    * @return
    */
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[NoSuchProcessException]("When no process exists for the given id")
  def processEventAsync(@Nonnull processId: UUID, @Nonnull event: Any, @Nonnull correlationId: String, @Nonnull timeout: java.time.Duration): BakerResponse =
    baker.processEventAsync(processId.toString, event, Some(correlationId), timeout.toScala)


  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @param timeout   the maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getIngredients(@Nonnull processId: String, @Nonnull timeout: java.time.Duration): java.util.Map[String, Value] =
    baker
      .getIngredients(processId, timeout.toScala)
      .asJava
      .asInstanceOf[java.util.Map[String, Value]]


  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @param timeout   The maximum wait time
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getIngredients(@Nonnull processId: UUID, @Nonnull timeout: java.time.Duration): java.util.Map[String, Value] =
    getIngredients(processId.toString, timeout)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(@Nonnull processId: String): java.util.Map[String, Value] =
    baker.getIngredients(processId).asJava

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getIngredients(@Nonnull processId: UUID): java.util.Map[String, Value] =
    getIngredients(processId.toString)

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @param timeout   The maximum wait time
    * @return
    *
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getEvents(@Nonnull processId: String, @Nonnull timeout: java.time.Duration): EventList =
    new EventList(baker.events(processId, timeout.toScala))

  /**
    * Returns all events that have occurred for a given process.
    *
    * Note that this list is eventually consistent. This means that it might take some
    * time before an event that occurred in the process is appended to the list.
    *
    * @param processId The process identifier
    * @param timeout   The maximum wait time
    * @return
    *
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the given deadline")
  def getEvents(@Nonnull processId: UUID, @Nonnull timeout: java.time.Duration): EventList =
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
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getEvents(@Nonnull processId: String): EventList =
    new EventList(baker.events(processId))

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
  @throws[ProcessDeletedException]("When no process is deleted")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getEvents(@Nonnull processId: UUID): EventList = getEvents(processId.toString)

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId the recipeId
    * @return The JRecipeInformation recipe
    */
  @throws[TimeoutException]("When the recipe is not found within the default deadline")
  def getRecipe(@Nonnull recipeId: String): RecipeInformation =
    baker.getRecipe(recipeId)

  /**
    * Returns the recipe information for the given recipeId
    *
    * @param recipeId the recipeId
    * @param timeout  the maxium wait time
    * @return The JRecipeInformation for the recipe
    */
  @throws[TimeoutException]("When the recipe is not found within the given deadline")
  def getRecipe(@Nonnull recipeId: String, @Nonnull timeout: java.time.Duration): RecipeInformation =
    baker.getRecipe(recipeId, timeout.toScala)

  /**
    * Returns the compiled recipe for the given recipeId
    *
    * @param recipeId the recipeId
    * @return The compiled recipe
    */
  @throws[TimeoutException]("When the compiled recipe is not found within the default deadline")
  def getCompiledRecipe(@Nonnull recipeId: String): CompiledRecipe =
    baker.getCompiledRecipe(recipeId)

  /**
    * Returns the compiled recipe for the given recipeId
    *
    * @param recipeId the recipeId
    * @param timeout  the maxium wait time
    * @return The compiled recipe
    */
  @throws[TimeoutException]("When the compiled recipe is not found within the given deadline")
  def getCompiledRecipe(@Nonnull recipeId: String, @Nonnull timeout: java.time.Duration): CompiledRecipe =
    baker.getCompiledRecipe(recipeId, timeout.toScala)

  /**
    * Return alls recipes added to this Baker
    *
    * @return A map with all recipes from recipeId -> JRecipeInformation
    */
  @throws[TimeoutException]("When the Baker does not respond within the default deadline")
  def getAllRecipes(): java.util.Map[String, RecipeInformation] =
    baker.getAllRecipes().asJava

  /**
    * Return alls recipes added to this Baker
    *
    * @param timeout
    * @return A map with all recipes from recipeId -> JRecipeInformation
    */
  @throws[TimeoutException]("When the Baker does not respond within the given deadline")
  def getAllRecipes(@Nonnull timeout: java.time.Duration): java.util.Map[String, RecipeInformation] =
    baker.getAllRecipes(timeout.toScala).asJava

  /**
    * Returns an index of all processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the given timeout.
    *
    * Does not include deleted processes.
    *
    * @param timeout
    * @return An index of all processes
    */
  def getIndex(@Nonnull timeout: java.time.Duration): java.util.Set[ProcessMetadata] =
    baker.getIndex(timeout.toScala).asJava

  /**
    * Returns an index of all processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the configured default inquire timeout (baker.process-inquire-timeout)
    *
    * Does not include deleted processes.
    *
    * @return An index of all processes
    */
  def getIndex(): java.util.Set[ProcessMetadata] =
    baker.getIndex().asJava

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
  def registerEventListener(@Nonnull recipeName: String, @Nonnull listener: EventListener): Unit = baker.registerEventListener(recipeName, listener)

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
  def registerEventListener(@Nonnull listener: EventListener): Unit = baker.registerEventListener(listener)


  /**
    * Registers a listener
    *
    * @param listener
    * @return
    */
  def registerBakerEventListener(@Nonnull listener: AnyRef) = {
    baker.registerEventListenerPF(new AnnotatedEventSubscriber(listener))
  }

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId The process identifier
    * @param timeout   The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getVisualState(@Nonnull processId: String, @Nonnull timeout: java.time.Duration): String =
    baker.getVisualState(processId, timeout.toScala)

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param processId The process identifier
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getProcessState(@Nonnull processId: String): ProcessState =
    baker.getProcessState(processId)

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param processId The process identifier
    * @param timeout   The maximum time to wait
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getProcessState(@Nonnull processId: String, @Nonnull timeout: java.time.Duration): ProcessState =
    baker.getProcessState(processId, timeout.toScala)

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param processId The process identifier
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getProcessState(@Nonnull processId: UUID): ProcessState =
    baker.getProcessState(processId.toString)

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param processId The process identifier
    * @param timeout   The maximum time to wait
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getProcessState(@Nonnull processId: UUID, @Nonnull timeout: java.time.Duration): ProcessState =
    baker.getProcessState(processId.toString, timeout.toScala)

  /**
    * Returns the event names of a process instance
    *
    * @param processId The process identifier
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getEventNames(@Nonnull processId: String): java.util.List[String] =
    baker.eventNames(processId).asJava

  /**
    * Returns the event names of a process instance
    *
    * @param processId The process identifier
    * @param timeout   The maximum time to wait
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getEventNames(@Nonnull processId: String, @Nonnull timeout: java.time.Duration): java.util.List[String] =
    baker.eventNames(processId, timeout.toScala).asJava

  /**
    * Returns the event names of a process instance
    *
    * @param processId The process identifier
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getEventNames(@Nonnull processId: UUID): java.util.List[String] =
    baker.eventNames(processId.toString).asJava

  /**
    * Returns the event names of a process instance
    *
    * @param processId The process identifier
    * @param timeout   The maximum time to wait
    * @return The state of the process instance
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getEventNames(@Nonnull processId: UUID, @Nonnull timeout: java.time.Duration): java.util.List[String] =
    baker.eventNames(processId.toString, timeout.toScala).asJava

  /**
    * Returns the visual state of the recipe in dot format
    *
    * @param processId The process identifier
    * @param timeout   The maximum time to wait
    * @return
    */
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getVisualState(@Nonnull processId: UUID, @Nonnull timeout: java.time.Duration): String =
    getVisualState(processId.toString, timeout)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(@Nonnull processId: String): String =
    baker.getVisualState(processId)

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  @throws[TimeoutException]("When the process does not respond within the default deadline")
  def getVisualState(@Nonnull processId: UUID): String =
    getVisualState(processId.toString)
}
