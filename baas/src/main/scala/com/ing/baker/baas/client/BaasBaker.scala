package com.ing.baker.baas.client

import akka.NotUsed
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.Marshal
import akka.http.scaladsl.model.HttpMethods._
import akka.http.scaladsl.model.{RequestEntity, _}
import akka.stream.scaladsl.{Framing, Source}
import com.ing.baker.baas.interaction.server.RemoteInteractionLauncher
import com.ing.baker.baas.server.protocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.events.BakerEvent
import com.ing.baker.runtime.common.{EventListener, InteractionImplementation, ProcessMetadata, RecipeInformation}
import com.ing.baker.runtime.akka.{BakerResponse, BakerResponseEventProtocol, ProcessState, RuntimeEvent}
import com.ing.baker.runtime.scaladsl.Baker
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
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  override def bake(recipeId: String, processId: String): Future[Unit] = {
    Marshal(BakeRequest(recipeId)).to[RequestEntity]
      .map { body =>
        HttpRequest(
          uri = s"$baseUri/$processId/bake",
          method = POST,
          entity = body)
      }
      .flatMap(doRequestAndParseResponse[BakeResponse])
      .map(_ => ())
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  override def processEvent(processId: String, event: Any): Future[BakerResponse] = {
    //Create request to give to Baker
//    log.info("Creating runtime event to fire")
//    val runtimeEvent = RuntimeEvent.extractEvent(event)
//
//    Marshal(ProcessEventRequest(runtimeEvent)).to[RequestEntity]
//      .map { body =>
//        HttpRequest(
//          uri = s"$baseUri/$processId/event",
//          method = POST,
//          entity = body)
//      }
//      .flatMap(doRequestAndParseResponse[ProcessEventResponse])
    ???
  }


  /**
    * Creates a stream of specific events.
    */
  def processEventStream(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): Future[Source[BakerResponseEventProtocol, NotUsed]] = {
    val runtimeEvent = RuntimeEvent.extractEvent(event)
    Marshal(ProcessEventRequest(runtimeEvent)).to[RequestEntity]
      .flatMap { body =>
        Http().singleRequest(HttpRequest(
          uri = s"$baseUri/$processId/event/stream",
          method = POST,
          entity = body))
      }.map { _.entity
        .dataBytes
        .via(Framing.delimiter(BakerResponseEventProtocol.SerializationDelimiter, maximumFrameLength = Int.MaxValue))
        .via(deserializeFlow[BakerResponseEventProtocol])
        .mapMaterializedValue(_ => NotUsed)
      }
  }

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  override def getProcessState(processId: String): Future[ProcessState] = {
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
  override def getIngredients(processId: String): Future[Map[String, Value]] = {
    getProcessState(processId).map(_.ingredients)
  }

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the process state.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(processId: String): Future[String] = {
    val request = HttpRequest(
      uri = s"$baseUri/$processId/visual_state",
      method = GET)
    doRequestAndParseResponse[VisualStateResponse](request).map(_.visualState)
  }


  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  override def addImplementation(implementation: AnyRef): Future[Unit] = {
    Future.successful(remoteInteractionLauncher.addImplementation(implementation))
  }

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addImplementations(implementations: Seq[AnyRef]): Future[Unit] = {
    Future.successful(implementations.foreach(addImplementation))
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  override def addImplementation(implementation: InteractionImplementation): Future[Unit] = {
    Future.successful(remoteInteractionLauncher.addImplementation(implementation))
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = ???

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  override def processEvent(processId: String, event: Any, correlationId: String): Future[BakerResponse] = ???

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
  override def getIndex(): Future[Set[ProcessMetadata]] = ???

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listener: EventListener): Future[Unit] = ???

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listener: EventListener): Future[Unit] = ???

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): Future[Unit] = ???

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(processId: String, interactionName: String): Future[Unit] = ???

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(processId: String, interactionName: String, event: Any): Future[Unit] = ???

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(processId: String, interactionName: String): Future[Unit] = ???

  /**
    * This registers a listener function.
    *
    * @param pf A partial function that receives the events.
    * @return
    */
  override def registerEventListenerPF(pf: PartialFunction[BakerEvent, Unit]): Future[Unit] = ???
}
