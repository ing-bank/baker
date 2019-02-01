package com.ing.baker.baas.client

import akka.NotUsed
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.Marshal
import akka.http.scaladsl.model.HttpMethods._
import akka.http.scaladsl.model.ws.WebSocketRequest
import akka.http.scaladsl.model.{RequestEntity, _}
import akka.stream.scaladsl.{Flow, Framing, Source}
import akka.util.ByteString
import com.ing.baker.baas.interaction.server.RemoteInteractionLauncher
import com.ing.baker.baas.server.protocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.process_instance.protobuf.TransitionNotEnabled
import com.ing.baker.runtime.core.events.BakerEvent
import com.ing.baker.runtime.core.{Baker, BakerResponse, BakerResponseEventProtocol, EventListener, InteractionImplementation, ProcessMetadata, ProcessState, RecipeInformation, RuntimeEvent, SensoryEventStatus}
import com.ing.baker.types.Value
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._
import org.slf4j.{Logger, LoggerFactory}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BaasBaker(config: Config,
                val clientHost: String,
                val clientPort: Int,
                val baasHost: String,
                val baasPort: Int)(implicit val actorSystem: ActorSystem) extends Baker with ClientUtils {

  val baseUri: String = s"http://$baasHost:$baasPort"

  private val remoteInteractionLauncher: RemoteInteractionLauncher = RemoteInteractionLauncher(clientHost, clientPort, baasHost, baasPort)
  Await.result(remoteInteractionLauncher.start(), 10 seconds)

  override val log: Logger = LoggerFactory.getLogger(classOf[BaasBaker])
  implicit val requestTimeout: FiniteDuration = 30 seconds

  override val defaultBakeTimeout: FiniteDuration = config.as[FiniteDuration]("baker.bake-timeout")
  override val defaultProcessEventTimeout: FiniteDuration = config.as[FiniteDuration]("baker.process-event-timeout")
  override val defaultInquireTimeout: FiniteDuration = config.as[FiniteDuration]("baker.process-inquire-timeout")
  override val defaultShutdownTimeout: FiniteDuration = config.as[FiniteDuration]("baker.shutdown-timeout")
  override val defaultAddRecipeTimeout: FiniteDuration = config.as[FiniteDuration]("baker.add-recipe-timeout")

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe, timeout: FiniteDuration): String = {
    val responseFuture: Future[AddRecipeResponse] =
      Marshal(AddRecipeRequest(compiledRecipe)).to[RequestEntity]
        .map { body =>
          HttpRequest(
            uri = baseUri + "/recipe",
            method = POST,
            entity = body)
        }.flatMap(doRequestAndParseResponse[AddRecipeResponse])
    Await.result(responseFuture, timeout)
      .recipeId
  }

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String, timeout: FiniteDuration): RecipeInformation = {
    val request = HttpRequest(
      uri = s"$baseUri/recipe/$recipeId",
      method = GET)
    Await.result(doRequestAndParseResponse[RecipeInformation](request), timeout)
  }

  /**
    * Returns the compiled recipe for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getCompiledRecipe(recipeId: String, timeout: FiniteDuration): CompiledRecipe = {
    val request = HttpRequest(
      uri = s"$baseUri/recipe/$recipeId",
      method = GET)
    val recipeInformation: RecipeInformation = Await.result(doRequestAndParseResponse[RecipeInformation](request), timeout)
    recipeInformation.compiledRecipe
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes(timeout: FiniteDuration): Map[String, RecipeInformation] = {
    throw new IllegalArgumentException("Not allowed to get all recipes")
  }

  /**
    * Returns a future of all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipesAsync(timeout: FiniteDuration): Future[Map[String, RecipeInformation]] = {
    throw new IllegalArgumentException("Not allowed to get all recipes")
  }

  /**
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  override def bake(recipeId: String, processId: String, timeout: FiniteDuration): ProcessState = {
    Await.result(bakeAsync(recipeId, processId, timeout), timeout)
  }

  /**
    * Asynchronously creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  override def bakeAsync(recipeId: String, processId: String, timeout: FiniteDuration): Future[ProcessState] = {
    Marshal(BakeRequest(recipeId)).to[RequestEntity]
      .map { body =>
        HttpRequest(
          uri = s"$baseUri/$processId/bake",
          method = POST,
          entity = body)
      }
      .flatMap(doRequestAndParseResponse[BakeResponse])
      .map(_.processState)
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  override def processEvent(processId: String, event: Any, correlationId: Option[String], timeout: FiniteDuration): SensoryEventStatus = {
    //Create request to give to Baker
    log.info("Creating runtime event to fire")
    val runtimeEvent = Baker.extractEvent(event)

    val response = Marshal(ProcessEventRequest(runtimeEvent)).to[RequestEntity]
      .map { body =>
        HttpRequest(
          uri = s"$baseUri/$processId/event",
          method = POST,
          entity = body)
      }
      .flatMap(doRequestAndParseResponse[ProcessEventResponse])
      .map(_.status)
    Await.result(response, timeout)

  }

  /**
    * Notifies Baker that an event has happened.
    *
    * If nothing is done with the BakerResponse there is NO guarantee that the event is received by the process instance.
    */
  override def processEventAsync(processId: String, event: Any, correlationId: Option[String], timeout: FiniteDuration): BakerResponse = {
    val source = Await.result(processEventStream(processId, event, correlationId, timeout), timeout)
    new BakerResponse(processId, source)
  }

  /**
    * Creates a stream of specific events.
    */
  override def processEventStream(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): Future[Source[BakerResponseEventProtocol, NotUsed]] = {
    val runtimeEvent = Baker.extractEvent(event)
    Marshal(ProcessEventRequest(runtimeEvent)).to[RequestEntity]
      .flatMap { body =>
        Http().singleRequest(HttpRequest(
          uri = s"$baseUri/$processId/event/stream",
          method = POST,
          entity = body))
      }.map { _.entity
        .dataBytes
        .via(deserializeFlow[BakerResponseEventProtocol])
        .mapMaterializedValue(_ => NotUsed)
      }
  }

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(processId: String, interactionName: String, timeout: FiniteDuration): Unit = {
    //TODO implement
  }

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(processId: String, interactionName: String, event: Any, timeout: FiniteDuration): Unit = {
    //TODO implement
  }

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(processId: String, interactionName: String, timeout: FiniteDuration): Unit = {
    //TODO implement
  }

  /**
    * Synchronously returns all event names that occurred for a process.
    */
  override def eventNames(processId: String, timeout: FiniteDuration): List[String] = {
    getProcessState(processId, timeout).eventNames
  }

  /**
    * Returns a stream of all events with their timestamps for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  override def eventsWithTimestampAsync(processId: String): Source[(RuntimeEvent, Long), NotUsed] = {
    //TODO implement and remove Source from Baker interface
    null
  }

  /**
    * Returns a stream of all events for a process.
    *
    * @param processId The process identifier.
    * @return A sequence of events with their timestamps.
    */
  override def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] = {
    //TODO implement
    null
  }

  /**
    * Synchronously returns a sequence of all events for a process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the events.
    */
  override def events(processId: String, timeout: FiniteDuration): Seq[RuntimeEvent] = {
    val request = HttpRequest(
      uri = s"$baseUri/$processId/events",
      method = GET)
    val events = doRequestAndParseResponse[EventsResponse](request).map(_.events)
    Await.result(events, timeout)
  }

  /**
    * Synchronously returns a sequence of all events with their timestamps for a process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the events.
    * @return A sequence of events with their timestamps.
    */
  override def eventsWithTimestamp(processId: String, timeout: FiniteDuration): Seq[(RuntimeEvent, Long)] = ???

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
  override def getIndex(timeout: FiniteDuration): Set[ProcessMetadata] = ???

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  override def getProcessState(processId: String, timeout: FiniteDuration): ProcessState = {
    Await.result(getProcessStateAsync(processId, timeout), timeout)
  }

  /**
    * returns a future with the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  override def getProcessStateAsync(processId: String, timeout: FiniteDuration): Future[ProcessState] = {
    val request = HttpRequest(
      uri = s"$baseUri/$processId/state",
      method = GET)
    doRequestAndParseResponse[StateResponse](request).map(_.processState)
  }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(processId: String, timeout: FiniteDuration): Map[String, Value] = {
    getProcessState(processId).ingredients
  }

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  override def getIngredientsAsync(processId: String, timeout: FiniteDuration): Future[Map[String, Value]] = {
    getProcessStateAsync(processId).map(_.ingredients)
  }

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the process state.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(processId: String, timeout: FiniteDuration): String = {
    val request = HttpRequest(
      uri = s"$baseUri/$processId/visual_state",
      method = GET)
    val response = doRequestAndParseResponse[VisualStateResponse](request).map(_.visualState)
    Await.result(response, timeout)
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listener: EventListener): Boolean = {
    //TODO implement
    false
  }

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listener: EventListener): Boolean = {
    //TODO implement
    false
  }

  /**
    * This registers a listener function.
    *
    * @param pf A partial function that receives the events.
    * @return
    */
  override def registerEventListenerPF(pf: PartialFunction[BakerEvent, Unit]): Boolean = {
    //TODO implement
    false
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  override def addImplementation(implementation: AnyRef): Unit = {
    remoteInteractionLauncher.addImplementation(implementation)
  }

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addImplementations(implementations: Seq[AnyRef]): Unit = {
    implementations.foreach(addImplementation)
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  override def addImplementation(implementation: InteractionImplementation): Unit = {
    remoteInteractionLauncher.addImplementation(implementation)
  }

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(timeout: FiniteDuration): Unit = {
    //TODO implement
  }


}
