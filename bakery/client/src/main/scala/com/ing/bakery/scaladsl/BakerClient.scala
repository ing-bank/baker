package com.ing.bakery.scaladsl

import cats.effect.{IO, Resource}
import com.ing.baker.il.RecipeVisualStyle
import com.ing.baker.runtime.common.BakerException.SingleInteractionExecutionFailedException
import com.ing.baker.runtime.common.{BakerException, RecipeRecord, SensoryEventStatus, Utils}
import com.ing.baker.runtime.scaladsl.{BakerEvent, BakerResult, EncodedRecipe, EventInstance, EventMoment, EventResolutions, IngredientInstance, InteractionExecutionResult, InteractionInstanceDescriptor, RecipeEventMetadata, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult, Baker => ScalaBaker}
import com.ing.baker.runtime.serialization.InteractionExecution
import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.types.Value
import com.ing.bakery.common.FailoverUtils._
import com.ing.bakery.common.{FailoverState, TLSConfig}
import com.typesafe.scalalogging.LazyLogging
import io.circe.Decoder
import org.http4s.Method._
import org.http4s._
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.blaze._
import org.http4s.client.dsl.io._

import scala.collection.immutable.Seq
import scala.concurrent.{ExecutionContext, Future}
import scala.util.control.NoStackTrace
import cats.effect.Temporal

object BakerClient {
  def resourceBalancedWithLegacyFallback(endpointConfig: EndpointConfig,
                                         fallbackEndpointConfig: Option[EndpointConfig] = None,
                                         executionContext: ExecutionContext,
                                         filters: Seq[Request[IO] => Request[IO]] = Seq.empty,
                                         tlsConfig: Option[TLSConfig] = None)
                                        (implicit timer: Temporal[IO]): Resource[IO, BakerClient] = {
    implicit val ex: ExecutionContext = executionContext

    BlazeClientBuilder[IO](executionContext, tlsConfig.map(_.loadSSLContext))
      .resource
      .map(client => {
        new BakerClient(client, endpointConfig, fallbackEndpointConfig, filters)
      })
  }

  def resourceBalanced(endpointConfig: EndpointConfig,
                       executionContext: ExecutionContext,
                       filters: Seq[Request[IO] => Request[IO]] = Seq.empty,
                       tlsConfig: Option[TLSConfig] = None)
                      (implicit timer: Temporal[IO]): Resource[IO, BakerClient] = {
    resourceBalancedWithLegacyFallback(endpointConfig, None, executionContext, filters, tlsConfig)
  }

  /**
    * Creates client to remote Baker cluster
    *
    * @param host             Baker host
    * @param apiUrlPrefix     Prefix of Baker API URL, from the root of the host
    * @param executionContext Execution Context
    * @param filters          Http Filters to be applied to the invocation pipeline
    * @param tlsConfig        TLSConfig
    * @param cs               Cat's implicits
    * @param timer            Cat's implicits
    * @return IO Resource for BakerClient
    */
  def resource(host: Uri,
               apiUrlPrefix: String,
               executionContext: ExecutionContext,
               filters: Seq[Request[IO] => Request[IO]] = Seq.empty,
               tlsConfig: Option[TLSConfig] = None,
               apiLoggingEnabled: Boolean = false)
              (implicit timer: Temporal[IO]): Resource[IO, BakerClient] =
    resourceBalanced(EndpointConfig(IndexedSeq(host), apiUrlPrefix, apiLoggingEnabled), executionContext, filters, tlsConfig)(cs, timer)


  def apply(client: Client[IO], host: Uri, apiUrlPrefix: String, filters: Seq[Request[IO] => Request[IO]], apiLoggingEnabled: Boolean = false)
           (implicit ec: ExecutionContext): BakerClient =
    new BakerClient(client, EndpointConfig(IndexedSeq(host), apiUrlPrefix, apiLoggingEnabled), None, filters)(ec)
}

class ResponseError(val status: Int, val msg: String)
  extends RuntimeException(status.toString + msg) with NoStackTrace {
}

object ResponseError {
  def apply(status: Int, msg: String) = new ResponseError(status, msg)

  def unapply(error: ResponseError): Some[(Int, String)] =
    Some((error.status, error.msg))
}

final case class EndpointConfig(hosts: IndexedSeq[Uri], apiUrlPrefix: String = "/api/bakery", apiLoggingEnabled: Boolean = false)

final class BakerClient( client: Client[IO],
                         endpoint: EndpointConfig,
                         fallbackEndpoint: Option[EndpointConfig],
                         filters: Seq[Request[IO] => Request[IO]] = Seq.empty)
                       (implicit ec: ExecutionContext) extends ScalaBaker with LazyLogging {

  implicit val eventInstanceResultEntityEncoder: EntityEncoder[IO, EventInstance] = jsonEncoderOf[IO, EventInstance]
  implicit val recipeEncoder: EntityEncoder[IO, EncodedRecipe] = jsonEncoderOf[IO, EncodedRecipe]
  implicit val interactionRequestEncoder: EntityEncoder[IO, InteractionExecution.ExecutionRequest] = jsonEncoderOf[IO, InteractionExecution.ExecutionRequest]

  override def addRecipe(recipe: RecipeRecord): Future[String] =
    callRemoteBakerService[String]((host, prefix) => POST(
      EncodedRecipe(
        base64 = new String(java.util.Base64.getEncoder.encode(Utils.recipeToByteArray(recipe.recipe)), "UTF-8"),
        createdAt = recipe.updated),
      root(host, prefix) / "app" / "recipes")).map { r =>
      logger.info(s"Result of adding a recipe: $r")
      r
    }

  private def parse[A](result: BakerResult)(implicit decoder: Decoder[A]): Either[Exception, A] = {
    result match {
      case BakerResult(BakerResult.Success, body) => body.as[A]
      case BakerResult(BakerResult.Error, body) => body.as[BakerException].flatMap(x => Left(x))
      case x => Left(new IllegalStateException(s"Can't process $x"))
    }
  }

  private def root(host: Uri, apiUrlPrefix: String): Uri = {
    val hostString = host.renderString
    val prefix = if (hostString.endsWith("/")) hostString.dropRight(1) else hostString
    val suffix = if (apiUrlPrefix.startsWith("/")) apiUrlPrefix.substring(1) else apiUrlPrefix
    val uriString = s"$prefix/$suffix"
    Uri.fromString(uriString).getOrElse(
      throw new IllegalArgumentException(s"API URI '$uriString' is not a valid URI")
    )
  }

  private def callRemoteBakerService[A](request: (Uri, String) => IO[Request[IO]])(implicit decoder: Decoder[A]): Future[A] =
    callRemoteBakerImpl(request, handleHttpErrors, None)(decoder)


  private def callRemoteBakerServiceFallbackAware[A](request: (Uri, String) => IO[Request[IO]],
                                                   fallbackEndpoint: Option[EndpointConfig])(implicit decoder: Decoder[A]): Future[A] =
    callRemoteBakerImpl(request, handleFallbackAwareErrors, fallbackEndpoint)(decoder)

  private def callRemoteBakerImpl[A](request: (Uri, String) => IO[Request[IO]],
                                     errorHandler: Response[IO] => IO[Throwable],
                                     fallbackEndpoint: Option[EndpointConfig])
                                    (implicit decoder: Decoder[A]): Future[A] = {
    callWithFailOver(new FailoverState(endpoint), client, request, filters, errorHandler, fallbackEndpoint)
      .map(r => {
        parse(r)(decoder)
      })
      .unsafeToFuture()
      .flatMap {
        case Left(bakerException: BakerException) =>
          logger.warn(s"Baker call resulted in Baker exception: ${bakerException.message}")
          Future.failed(bakerException)
        case Left(t) =>
          logger.error(s"Request $request sent to remote Baker caused unexpected error", t)
          Future.failed(t)
        case Right(t) => Future.successful(t)
      }
  }

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[RecipeInformation] =
    callRemoteBakerService[RecipeInformation]((host, prefix) => GET(root(host, prefix) / "app" / "recipes" / recipeId))

  override def getRecipeVisual(recipeId: String, style: RecipeVisualStyle): Future[String] =
    callRemoteBakerService[String]((host, prefix) => GET(root(host, prefix) / "app" / "recipes" / recipeId / "visual"))

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] =
    callRemoteBakerService[Map[String, RecipeInformation]]( (host, prefix) => GET(root(host, prefix) / "app" / "recipes"))

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] =
    callRemoteBakerService[Unit]((host, prefix) => POST(root(host, prefix) / "instances" / recipeInstanceId / "bake" / recipeId)).map { _ =>
      logger.info(s"Baked recipe instance '$recipeInstanceId' from recipe '$recipeId'")
    }


  override def getInteraction(interactionName: String): Future[Option[InteractionInstanceDescriptor]] =
    callRemoteBakerService[Option[InteractionInstanceDescriptor]]((host, prefix) => GET(root(host, prefix) / "app" / "interactions" / interactionName))


  override def getAllInteractions: Future[List[InteractionInstanceDescriptor]] =
    callRemoteBakerService[List[InteractionInstanceDescriptor]]((host, prefix) => GET(root(host, prefix) / "app" / "interactions"))

  override def executeSingleInteraction(interactionId: String, ingredients: Seq[IngredientInstance]): Future[InteractionExecutionResult] =
    callRemoteBakerService[InteractionExecution.ExecutionResult]((host, prefix) =>
      POST(InteractionExecution.ExecutionRequest(interactionId, ingredients.toList), root(host, prefix) / "app" / "interactions" / "execute")).map{ result =>
        result.outcome match {
          case Left(failure) => InteractionExecutionResult(Left(failure.toBakerInteractionExecutionFailure))
          case Right(success) => InteractionExecutionResult(Right(success.toBakerInteractionExecutionSuccess))
        }
      }

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
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String,
                                                event: EventInstance,
                                                correlationId: Option[String]): Future[SensoryEventResult] =
    callRemoteBakerServiceFallbackAware[SensoryEventResult](
      (host, prefix) => POST(event, (root(host, prefix) / "instances" / recipeInstanceId / "fire-and-resolve-when-completed")
        .withOptionQueryParam("correlationId", correlationId)), fallbackEndpoint).map { result =>
      logger.info(s"For recipe instance '$recipeInstanceId', fired and completed event '${event.name}', resulting status ${result.sensoryEventStatus}")
      logger.debug(s"Resulting ingredients ${result.ingredients.map { case (ingredient, value) => s"$ingredient=$value" }.mkString(", ")}")
      result
    }

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
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String,
                                               event: EventInstance,
                                               correlationId: Option[String]): Future[SensoryEventStatus] =
    callRemoteBakerServiceFallbackAware[SensoryEventStatus](
      (host, prefix) => POST(event, (root(host, prefix) / "instances" / recipeInstanceId / "fire-and-resolve-when-received")
        .withOptionQueryParam("correlationId", correlationId)), fallbackEndpoint).map { result =>
      logger.info(s"For recipe instance '$recipeInstanceId', fired and received event '${event.name}', resulting status $result")
      result
    }

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
  override def fireEventAndResolveOnEvent(recipeInstanceId: String,
                                          event: EventInstance,
                                          onEvent: String,
                                          correlationId: Option[String]): Future[SensoryEventResult] =
    callRemoteBakerServiceFallbackAware[SensoryEventResult](
      (host, prefix) => POST(event, (root(host, prefix) / "instances" / recipeInstanceId / "fire-and-resolve-on-event" / onEvent)
        .withOptionQueryParam("correlationId", correlationId)), fallbackEndpoint).map { result =>
      logger.info(s"For recipe instance '$recipeInstanceId', fired event '${event.name}', and resolved on event '$onEvent', resulting status ${result.sensoryEventStatus}")
      logger.debug(s"Resulting ingredients ${result.ingredients.map { case (ingredient, value) => s"$ingredient=$value" }.mkString(", ")}")
      result
    }


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
  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions =
    throw new NotImplementedError("Multiple events via HTTP API are not supported")

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
  override def getAllRecipeInstancesMetadata: Future[Set[RecipeInstanceMetadata]] =
    callRemoteBakerServiceFallbackAware[Set[RecipeInstanceMetadata]]((host, prefix) => GET(root(host, prefix) / "instances"), fallbackEndpoint)

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
    callRemoteBakerServiceFallbackAware[RecipeInstanceState]((host, prefix) => GET(root(host, prefix) / "instances" / recipeInstanceId), fallbackEndpoint)

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
    callRemoteBakerServiceFallbackAware[Map[String, Value]]((host, prefix) => GET(root(host, prefix) / "instances" / recipeInstanceId / "ingredients"), fallbackEndpoint)

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
    callRemoteBakerServiceFallbackAware[List[EventMoment]]((host, prefix) => GET(root(host, prefix) / "instances" / recipeInstanceId / "events"), fallbackEndpoint)

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  override def getEventNames(recipeInstanceId: String): Future[Seq[String]] =
    getEvents(recipeInstanceId).map(_.map(_.name))

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): Future[String] =
    callRemoteBakerServiceFallbackAware[String]((host, prefix) => GET(root(host, prefix) / "instances" / recipeInstanceId / "visual"), fallbackEndpoint)

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
    throw new NotImplementedError("registerEventListener is not implemented for client bakers")

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
    throw new NotImplementedError("registerEventListener is not implemented for client bakers")

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] =
    throw new NotImplementedError("registerBakerEventListener is not implemented for client bakers")

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): Future[Unit] =
    throw new NotImplementedError("Use the cats.effect.Resource mechanisms for this, you probably don't need to do anything, safe to ignore")

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
    callRemoteBakerServiceFallbackAware[Unit]((host, apiUrlPrefix) => POST(root(host, apiUrlPrefix) / "instances" / recipeInstanceId / "interaction" / interactionName / "retry"), fallbackEndpoint)

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] =
    callRemoteBakerServiceFallbackAware[Unit]((host, prefix) => POST(event, root(host, prefix) / "instances" / recipeInstanceId / "interaction" / interactionName / "resolve"), fallbackEndpoint)

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
    callRemoteBakerServiceFallbackAware[Unit]((host, prefix) => POST(root(host, prefix) / "instances" / recipeInstanceId / "interaction" / interactionName / "stop-retrying"), fallbackEndpoint)
}
