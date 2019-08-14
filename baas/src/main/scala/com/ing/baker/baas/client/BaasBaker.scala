package com.ing.baker.baas.client

import akka.actor.ActorSystem
import akka.http.scaladsl.marshalling.Marshal
import akka.http.scaladsl.model.HttpMethods._
import akka.http.scaladsl.model.{RequestEntity, _}
import com.ing.baker.baas.interaction.server.RemoteInteractionLauncher
import com.ing.baker.baas.server.protocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl._
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

  val defaultBakeTimeout: FiniteDuration = config.as[FiniteDuration]("baker.bake-timeout")
  val defaultProcessEventTimeout: FiniteDuration = config.as[FiniteDuration]("baker.process-event-timeout")
  val defaultInquireTimeout: FiniteDuration = config.as[FiniteDuration]("baker.process-inquire-timeout")
  val defaultShutdownTimeout: FiniteDuration = config.as[FiniteDuration]("baker.shutdown-timeout")
  val defaultAddRecipeTimeout: FiniteDuration = config.as[FiniteDuration]("baker.add-recipe-timeout")

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe): Future[String] = {
      Marshal(AddRecipeRequest(compiledRecipe)).to[RequestEntity]
        .map { body =>
          HttpRequest(
            uri = baseUri + "/recipe",
            method = POST,
            entity = body)
        }.flatMap(doRequestAndParseResponse[AddRecipeResponse])
      .map(_.recipeId)
  }

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[RecipeInformation] = {
    val request = HttpRequest(
      uri = s"$baseUri/recipe/$recipeId",
      method = GET)
    doRequestAndParseResponse[RecipeInformation](request)
  }

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] = {
    Marshal(BakeRequest(recipeId)).to[RequestEntity]
      .map { body =>
        HttpRequest(
          uri = s"$baseUri/$recipeInstanceId/bake",
          method = POST,
          entity = body)
      }
      .flatMap(doRequestAndParseResponse[BakeResponse])
      .map(_ => ())
  }

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    *   `NoSuchProcessException` -> When no process exists for the given id
    *   `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event     The event object
    */
  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] = ???

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    *   `NoSuchProcessException` -> When no process exists for the given id
    *   `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event     The event object
    */
  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[EventResult] = ???

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    *   `NoSuchProcessException` -> When no process exists for the given id
    *   `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event     The event object
    */
  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = ???

  /**
    * Creates a stream of specific events.
    */
  /*
  def processEventStream(RecipeInstanceId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): Future[Source[BakerResponseEventProtocol, NotUsed]] = {
    val runtimeEvent = RuntimeEvent.unsafeFrom(event)
    Marshal(ProcessEventRequest(runtimeEvent)).to[RequestEntity]
      .flatMap { body =>
        Http().singleRequest(HttpRequest(
          uri = s"$baseUri/$RecipeInstanceId/event/stream",
          method = POST,
          entity = body))
      }.map { _.entity
        .dataBytes
        .via(Framing.delimiter(BakerResponseEventProtocol.SerializationDelimiter, maximumFrameLength = Int.MaxValue))
        .via(deserializeFlow[BakerResponseEventProtocol])
        .mapMaterializedValue(_ => NotUsed)
      }
  }
   */

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] = {
    val request = HttpRequest(
      uri = s"$baseUri/$recipeInstanceId/state",
      method = GET)
    doRequestAndParseResponse[StateResponse](request).map(_.processState)
  }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] = {
    getRecipeInstanceState(recipeInstanceId).map(_.ingredients)
  }

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): Future[String] = {
    val request = HttpRequest(
      uri = s"$baseUri/$recipeInstanceId/visual_state",
      method = GET)
    doRequestAndParseResponse[VisualStateResponse](request).map(_.visualState)
  }

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addInteractionInstance(implementations: Seq[InteractionInstance]): Future[Unit] = {
    Future.successful(implementations.foreach(addInteractionInstance))
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  override def addInteractionInstance(implementation: InteractionInstance): Future[Unit] = {
    Future.successful(remoteInteractionLauncher.addImplementation(implementation))
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = ???

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
  override def getAllRecipeInstancesMetadata: Future[Set[RecipeInstanceMetadata]] = ???

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): Future[Unit] = ???

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = ???

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] = ???

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = ???

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (String, EventInstance) => Unit): Future[Unit] = ???

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listenerFunction: (String, EventInstance) => Unit): Future[Unit] = ???

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] = ???

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
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): Future[EventResult] = ???

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] = ???

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  override def getEventNames(recipeInstanceId: String): Future[Seq[String]] = ???
}
