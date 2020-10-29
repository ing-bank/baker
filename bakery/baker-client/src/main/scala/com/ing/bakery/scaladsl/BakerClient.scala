package com.ing.bakery.scaladsl

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{BakerEvent, BakerResult, EventInstance, EventMoment, EventResolutions, InteractionInstance, RecipeEventMetadata, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult, Baker => ScalaBaker}
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.types.Value
import com.ing.bakery.common.{FailoverState, FailoverUtils, TLSConfig}
import com.typesafe.scalalogging.LazyLogging
import io.circe.Decoder
import org.http4s.Method._
import org.http4s._
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.blaze._
import org.http4s.client.dsl.io._

import scala.concurrent.{ExecutionContext, Future}
import scala.util.control.NoStackTrace

object BakerClient {

  /** Use method `use` of the Resource, the client will be acquired and shut down automatically each time
    * the resulting `IO` is run, each time using the common connection pool.
    *
    * This method supports fail over to next host, available in list to support multi datacenters.
    * @param hosts Lists of hosts (multiple is supported for several DC)
    * @param executionContext Execution Context
    * @param filters Http Filters to be applied to the invocation pipeline
    * @param tlsConfig TLSConfig
    * @param cs Cat's implicits
    * @param timer Cat's implicits
    *
    * @return IO Resource for BakerClient
    */

  def resourceBalanced(hosts: IndexedSeq[Uri],
                       apiUrlPrefix: String,
                       executionContext: ExecutionContext,
                       filters: Seq[Request[IO] => Request[IO]] = Seq.empty,
                       tlsConfig: Option[TLSConfig] = None)
                      (implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, BakerClient] = {
    implicit val ex: ExecutionContext = executionContext

    BlazeClientBuilder[IO](executionContext, tlsConfig.map(_.loadSSLContext))
      .resource
      .map(client => {
        new BakerClient(client, hosts, apiUrlPrefix, filters)
      })
  }

  /**
    * Creates client to remote Baker cluster
    *
    * @param host Baker host
    * @param executionContext Execution Context
    * @param filters Http Filters to be applied to the invocation pipeline
    * @param tlsConfig TLSConfig
    * @param cs Cat's implicits
    * @param timer Cat's implicits
    *
    * @return IO Resource for BakerClient
    */
  def resource(host: Uri,
               apiUrlPrefix: String,
               executionContext: ExecutionContext,
               filters: Seq[Request[IO] => Request[IO]] = Seq.empty,
               tlsConfig: Option[TLSConfig] = None)
              (implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, BakerClient] =
    resourceBalanced(IndexedSeq(host), apiUrlPrefix, executionContext, filters, tlsConfig)(cs, timer)


  def apply(client: Client[IO], host: Uri, apiUrlPrefix: String, filters: Seq[Request[IO] => Request[IO]])
           (implicit ec: ExecutionContext): BakerClient =
    new BakerClient(client, IndexedSeq(host), apiUrlPrefix, filters)(ec)
}

final case class ResponseError(status: Int, msg: String)
  extends RuntimeException(status.toString + msg) with NoStackTrace

final class BakerClient(
                         client: Client[IO],
                         hosts: IndexedSeq[Uri],
                         apiUrlPrefix: String,
                         filters: Seq[Request[IO] => Request[IO]] = Seq.empty)
                       (implicit ec: ExecutionContext) extends ScalaBaker with LazyLogging {

  implicit val eventInstanceResultEntityEncoder: EntityEncoder[IO, EventInstance] = jsonEncoderOf[IO, EventInstance]

  override def addRecipe(compiledRecipe: CompiledRecipe): Future[String] =
    Future.failed(new NotImplementedError("Adding recipe via HTTP API is not supported"))

  private def parse[A](result: BakerResult)(implicit decoder: Decoder[A]): Either[Exception, A] = {
    result match {
      case BakerResult(BakerResult.Success, body) => body.as[A]
      case BakerResult(BakerResult.Error, body) => body.as[BakerException].flatMap(x => Left(x))
      case x => Left(new IllegalStateException(s"Can't process $x"))
    }
  }

  private def root(host: Uri): Uri = {
    val hostString = host.renderString
    val prefix = if (hostString.endsWith("/")) hostString.dropRight(1) else hostString
    val suffix = if (apiUrlPrefix.startsWith("/")) apiUrlPrefix.substring(1) else apiUrlPrefix
    val uriString = s"$prefix/$suffix"
    Uri.fromString(uriString).getOrElse(
      throw new IllegalArgumentException(s"API URI '$uriString' is not a valid URI")
    )
  }

  private def handleHttpErrors(errorResponse: Response[IO]): IO[Throwable] =
    errorResponse.bodyText.compile.foldMonoid.map(body => ResponseError(errorResponse.status.code, body))

  private def callRemoteBaker[A](request: Uri => IO[Request[IO]])
                                           (implicit decoder: Decoder[A]): Future[A] = {
    val fos = new FailoverState(hosts)

    FailoverUtils.callWithFailOver(fos, client, request, filters, handleHttpErrors)
      .map(r => { parse(r)(decoder)})
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
  override def getRecipe(recipeId: String): Future[RecipeInformation] = callRemoteBaker[RecipeInformation](uri => GET(root(uri) / "app" / "recipes" / recipeId))

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = callRemoteBaker[Map[String, RecipeInformation]](uri => GET(root(uri) / "app" / "recipes"))

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] =
    callRemoteBaker[Unit](host => POST(root(host) / "instances" / recipeInstanceId / "bake" / recipeId)).map { _ =>
      logger.info(s"Baked recipe instance '$recipeInstanceId' from recipe '$recipeId'")
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
    callRemoteBaker[SensoryEventResult](
      host => POST(event, (root(host) / "instances" / recipeInstanceId / "fire-and-resolve-when-completed")
        .withOptionQueryParam("correlationId", correlationId))).map { result =>
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
    callRemoteBaker[SensoryEventStatus](
      host => POST(event, (root(host) / "instances" / recipeInstanceId / "fire-and-resolve-when-received")
        .withOptionQueryParam("correlationId", correlationId))).map { result =>
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
    callRemoteBaker[SensoryEventResult](
      host => POST(event, (root(host) / "instances" / recipeInstanceId / "fire-and-resolve-on-event" / onEvent)
        .withOptionQueryParam("correlationId", correlationId))).map { result =>
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
    callRemoteBaker[Set[RecipeInstanceMetadata]](host => GET(root(host) / "instances"))

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
    callRemoteBaker[RecipeInstanceState](host => GET(root(host) / "instances" / recipeInstanceId))

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
    callRemoteBaker[Map[String, Value]](host => GET(root(host) / "instances" / recipeInstanceId / "ingredients"))

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
    callRemoteBaker[List[EventMoment]](host => GET(root(host) / "instances" / recipeInstanceId / "events"))

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
    callRemoteBaker[String](host => GET(root(host) / "instances" / recipeInstanceId / "visual"))

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
    * Adds an interaction implementation to baker.
    *
    * @param implementation The implementation object
    */
  override def addInteractionInstance(implementation: InteractionInstance): Future[Unit] =
    throw new NotImplementedError("addInteractionInstance is not implemented for client bakers, instances are deployed independently, please view the documentation")

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addInteractionInstances(implementations: Seq[InteractionInstance]): Future[Unit] =
    throw new NotImplementedError("addInteractionInstances is not implemented for client bakers, instances are deployed independently, please view the documentation")

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
    callRemoteBaker[Unit](host => POST(root(host) / "instances" / recipeInstanceId / "interaction" / interactionName / "retry"))

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] =
    callRemoteBaker[Unit](host => POST(event, root(host) / "instances" / recipeInstanceId / "interaction" / interactionName / "resolve"))

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
    callRemoteBaker[Unit](host => POST(root(host) / "instances" / recipeInstanceId / "interaction" / interactionName / "stop-retrying"))
}
