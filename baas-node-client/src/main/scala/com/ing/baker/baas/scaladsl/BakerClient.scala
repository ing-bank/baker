package com.ing.baker.baas.scaladsl

import java.io.{File, FileInputStream, InputStream}
import java.security.{KeyStore, SecureRandom}
import java.util.concurrent.Executors

import cats.implicits._
import cats.effect.{Blocker, ContextShift, IO, Resource, Timer}
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.baas.common.TLSConfig
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{BakerEvent, BakerResult, EventInstance, EventMoment, EventResolutions, InteractionInstance, RecipeEventMetadata, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult, Baker => ScalaBaker}
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging
import io.circe.{Decoder, DecodingFailure}
import javax.net.ssl.{KeyManagerFactory, SSLContext, TrustManagerFactory}
import org.http4s.Method.{POST, _}
import org.http4s._
import org.http4s.circe._
import org.http4s.client.blaze._
import org.http4s.client.dsl.io._
import org.http4s.client.{Client, JavaNetClientBuilder}

import scala.concurrent.{ExecutionContext, Future}

object BakerClient {

  def loadSSLContext(config: TLSConfig): SSLContext = {
    // Try resource directory as root first
    val keystoreResource: InputStream = getClass.getClassLoader.getResourceAsStream(config.keystorePath)
    // Otherwise try absolute path
    val keystore: InputStream =
      if(keystoreResource == null) new FileInputStream(new File(config.keystorePath))
      else keystoreResource
    require(keystore != null, s"Keystore of type '${config.keystoreType}' not found on path '${config.keystorePath}', tried classpath resources and then absolute path")
    loadSSLContextFromInputStream(keystore, config.password, config.keystoreType)
  }

  def loadSSLContextFromInputStream(keystore: InputStream, password: String, keystoreType: String): SSLContext = {
    val ks: KeyStore = KeyStore.getInstance(keystoreType)
    val passwordArray: Array[Char] = password.toCharArray
    ks.load(keystore, passwordArray)
    val keyManagerFactory: KeyManagerFactory = KeyManagerFactory.getInstance("SunX509")
    keyManagerFactory.init(ks, passwordArray)
    val tmf: TrustManagerFactory = TrustManagerFactory.getInstance("SunX509")
    tmf.init(ks)
    val sslContext: SSLContext = SSLContext.getInstance("TLS")
    sslContext.init(keyManagerFactory.getKeyManagers, tmf.getTrustManagers, new SecureRandom)
    sslContext
  }

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
    * the resulting `IO` is run, each time using the common connection pool.
    */
  def resource(hostname: Uri, pool: ExecutionContext, filters: Seq[Request[IO] => Request[IO]] = Seq.empty, tlsConfig: Option[TLSConfig] = None)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, BakerClient] = {
    implicit val ev0 = pool
    BlazeClientBuilder[IO](pool, tlsConfig.map(loadSSLContext))
      .resource
      .map(client => {
        new BakerClient(client, hostname, filters)
      })
  }
}

final class BakerClient(client: Client[IO], hostname: Uri, filters: Seq[Request[IO] => Request[IO]] = Seq.empty)(implicit ec: ExecutionContext) extends ScalaBaker with LazyLogging {

  val Root = hostname / "api" / "bakery"

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

  private def callRemoteBaker[A](request: IO[Request[IO]])(implicit decoder: Decoder[A]): Future[A] = {
    client.expect(request.map({ request: Request[IO] =>
      filters.foldLeft(request)((acc, filter) => filter(acc))
    }))(jsonOf[IO, BakerResult]).map(r => {
      parse(r)(decoder)
    }).unsafeToFuture() flatMap {
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
  override def getRecipe(recipeId: String): Future[RecipeInformation] = callRemoteBaker[RecipeInformation](GET(Root / "app" / "recipes" / recipeId))

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = callRemoteBaker[Map[String, RecipeInformation]](GET(Root / "app" / "recipes"))

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] =
    callRemoteBaker[Unit](POST(Root / "instances" / recipeInstanceId / "bake"  / recipeId)).map { _ =>
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
      POST(event, (Root / "instances" / recipeInstanceId / "fire-and-resolve-when-completed")
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
      POST(event, (Root / "instances" / recipeInstanceId / "fire-and-resolve-when-received")
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
      POST(event, (Root / "instances" / recipeInstanceId / "fire-and-resolve-on-event" / onEvent)
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
    callRemoteBaker[Set[RecipeInstanceMetadata]](GET(Root / "instances"))
  
  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
    callRemoteBaker[RecipeInstanceState](GET(Root / "instances" / recipeInstanceId))

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
    callRemoteBaker[Map[String, Value]](GET(Root / "instances" / recipeInstanceId / "ingredients"))

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
    callRemoteBaker[List[EventMoment]](GET(Root / "instances" / recipeInstanceId / "events"))

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
    callRemoteBaker[String](GET(Root / "instances" / recipeInstanceId / "visual"))

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
    callRemoteBaker[Unit](POST(Root / "instances" / recipeInstanceId / "interaction" / interactionName / "retry"))

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] =
    callRemoteBaker[Unit](POST(event, Root / "instances" / recipeInstanceId / "interaction" / interactionName / "resolve"))

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
    callRemoteBaker[Unit](POST(Root / "instances" / recipeInstanceId / "interaction" / interactionName / "stop-retrying"))

}
