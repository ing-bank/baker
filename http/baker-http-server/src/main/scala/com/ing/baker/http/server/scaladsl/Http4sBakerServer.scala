package com.ing.baker.http.server.scaladsl

import cats.data.OptionT
import cats.effect.unsafe.implicits.global
import cats.effect.{IO, Resource, Sync}
import cats.implicits._
import com.ing.baker.http.server.common.RecipeLoader
import com.ing.baker.http.{Dashboard, DashboardConfiguration}
import com.ing.baker.runtime.common.{BakerException, RecipeRecord}
import com.ing.baker.runtime.javadsl.{Baker => JBaker}
import com.ing.baker.runtime.scaladsl.{Baker, BakerResult, EncodedRecipe, EventInstance}
import com.ing.baker.runtime.serialization.InteractionExecution
import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.typesafe.config.{Config, ConfigFactory}
import com.typesafe.scalalogging.LazyLogging
import io.circe._
import io.circe.generic.auto._
import io.prometheus.client.CollectorRegistry
import org.http4s._
import org.http4s.blaze.server.BlazeServerBuilder
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.headers.{`Content-Length`, `Content-Type`}
import org.http4s.implicits._
import org.http4s.metrics.MetricsOps
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.middleware.{CORS, Logger, Metrics}
import org.http4s.server.{Router, Server}
import org.slf4j.LoggerFactory

import java.io.Closeable
import java.net.InetSocketAddress
import java.nio.charset.Charset
import java.util.concurrent.{CompletableFuture, TimeUnit}
import scala.concurrent.duration.{DurationInt, FiniteDuration}
import scala.concurrent.{ExecutionContext, Future}
import scala.jdk.FutureConverters.FutureOps

object Http4sBakerServer extends LazyLogging {

  def resource(baker: Baker, ec: ExecutionContext, hostname: InetSocketAddress, apiUrlPrefix: String,
               dashboardConfiguration: DashboardConfiguration, loggingEnabled: Boolean)
              (implicit sync: Sync[IO]): Resource[IO, Server] = {


    val apiLoggingAction: Option[String => IO[Unit]] = if (loggingEnabled) {
      val apiLogger = LoggerFactory.getLogger("API")
      Some(s => IO(apiLogger.info(s)))
    } else None

    for {
      metrics <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_api")
      server <- BlazeServerBuilder[IO](ec)
        .bindSocketAddress(hostname)
        .withHttpApp(
          CORS.policy
            .withAllowOriginAll
            .withAllowCredentials(true)
            .withMaxAge(1.day)(
              Logger.httpApp(
                logHeaders = loggingEnabled,
                logBody = loggingEnabled,
                logAction = apiLoggingAction)(
                routes(baker, apiUrlPrefix, metrics, dashboardConfiguration).orNotFound)))
        .resource
    } yield server
  }

  def resource(baker: Baker,
               http4sBakerServerConfiguration: Http4sBakerServerConfiguration,
               dashboardConfiguration: DashboardConfiguration,
               ec: ExecutionContext = ExecutionContext.global)
              (implicit sync: Sync[IO]): Resource[IO, Server] =
    resource(baker, ec,
      hostname = InetSocketAddress.createUnresolved(http4sBakerServerConfiguration.apiHost, http4sBakerServerConfiguration.apiPort),
      apiUrlPrefix = http4sBakerServerConfiguration.apiUrlPrefix,
      dashboardConfiguration = dashboardConfiguration,
      loggingEnabled = http4sBakerServerConfiguration.loggingEnabled
    )

  def java(baker: JBaker,
           http4sBakerServerConfiguration: Http4sBakerServerConfiguration,
           dashboardConfiguration: DashboardConfiguration,
          ): CompletableFuture[ClosableBakerServer] = {
    val serverStarted = resource(baker.getScalaBaker, http4sBakerServerConfiguration, dashboardConfiguration)
      .allocated
      .unsafeToFuture()
      .map {
        case (server: Server, closeEffect: IO[Unit]) => new ClosableBakerServer(server, closeEffect)
      }(ExecutionContext.global)
    serverStarted.asJava.toCompletableFuture
  }

  def java(baker: JBaker): CompletableFuture[ClosableBakerServer] = {
    val config: Config = ConfigFactory.load()
    java(baker, Http4sBakerServerConfiguration.fromConfig(config), DashboardConfiguration.fromConfig(config))
  }

  class ClosableBakerServer(val server: Server, closeEffect: IO[Unit]) extends Closeable {
    override def close(): Unit = closeEffect.unsafeRunSync()
  }

  def routes(baker: Baker, apiUrlPrefix: String, metrics: MetricsOps[IO],
             dashboardConfiguration: DashboardConfiguration)
            (implicit sync: Sync[IO]): HttpRoutes[IO] = {
    val dashboardRoutesOrEmpty: HttpRoutes[IO] =
      if (dashboardConfiguration.enabled) dashboardRoutes(apiUrlPrefix, dashboardConfiguration)
      else HttpRoutes.empty

    new Http4sBakerServer(baker).routesWithPrefixAndMetrics(apiUrlPrefix, metrics) <+> dashboardRoutesOrEmpty
  }


  private def dashboardRoutes(apiUrlPrefix: String, dashboardConfiguration: DashboardConfiguration)
                             (implicit sync: Sync[IO]): HttpRoutes[IO] =
    HttpRoutes.of[IO] {
      case GET -> Root / "dashboard_config" =>
        val bodyText = Dashboard.dashboardConfigJson(apiUrlPrefix, dashboardConfiguration)
        IO(Response[IO](
          status = Ok,
          body = fs2.Stream(bodyText).through(fs2.text.utf8Encode),
          headers = Headers(
            `Content-Type`(MediaType.text.plain, org.http4s.Charset.`UTF-8`),
            `Content-Length`.unsafeFromLong(bodyText.length)
          )
        ))
      case req if req.method == GET && req.pathInfo.renderString.matches(Dashboard.indexPattern.regex) =>
        dashboardFile(req, "index.html").getOrElseF(NotFound())

      case req if req.method == GET && Dashboard.files.contains(req.pathInfo.toRelative.renderString) =>
        dashboardFile(req, req.pathInfo.toRelative.renderString).getOrElseF(NotFound())
    }

  private def dashboardFile(request: Request[IO], filename: String)
                           (implicit sync: Sync[IO]): OptionT[IO, Response[IO]] = {
    OptionT.fromOption(Dashboard.safeGetResourcePath(filename))(sync)
      .flatMap(resourcePath => StaticFile.fromResource(resourcePath, Some(request)))
  }

  implicit val eventInstanceDecoder: EntityDecoder[IO, EventInstance] = jsonOf[IO, EventInstance]
  implicit val interactionExecutionRequestDecoder: EntityDecoder[IO, InteractionExecution.ExecutionRequest] = jsonOf[IO, InteractionExecution.ExecutionRequest]
  implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]
  implicit val recipeDecoder: EntityDecoder[IO, EncodedRecipe] = jsonOf[IO, EncodedRecipe]

  implicit class BakerResultIOHelper[A](io: => IO[A]) {
    def toBakerResultResponseIO(implicit encoder: Encoder[A]): IO[Response[IO]] =
      io.attempt.flatMap {
        case Left(e: BakerException) => Ok(BakerResult(e))
        case Left(e) =>
          logger.error(s"Unexpected exception happened when calling Baker", e)
          InternalServerError(s"No other exception but BakerExceptions should be thrown here: ${e.getCause}")
        case Right(()) => Ok(BakerResult.Ack)
        case Right(a) => Ok(BakerResult(a))
      }
  }
}

final class Http4sBakerServer private(baker: Baker) extends LazyLogging {

  object CorrelationId extends OptionalQueryParamDecoderMatcher[String]("correlationId")

  object Timeout extends QueryParamDecoderMatcher[Long]("timeout")

  object RemoveFromIndex extends OptionalQueryParamDecoderMatcher[Boolean]("removeFromIndex")

  private class RegExpValidator(regexp: String) {
    def unapply(str: String): Option[String] = if (str.matches(regexp)) Some(str) else None
  }

  private object RecipeId extends RegExpValidator("[A-Za-z0-9]+")

  private object RecipeInstanceId extends RegExpValidator("[A-Za-z0-9-]+")

  private object InteractionName extends RegExpValidator("[A-Za-z0-9_]+")

  private object IngredientName extends RegExpValidator("[A-Za-z0-9_]+")

  import Http4sBakerServer._

  def routesWithPrefixAndMetrics(apiUrlPrefix: String, metrics: MetricsOps[IO]): HttpRoutes[IO] =
    Router(
      apiUrlPrefix -> Metrics[IO](metrics, classifierF = metricsClassifier(apiUrlPrefix))(routes),
    )

  def routes: HttpRoutes[IO] = app <+> instance

  private def app: HttpRoutes[IO] = Router("/app" ->
    HttpRoutes.of[IO] {
      case GET -> Root / "health" => Ok()

      case GET -> Root / "interactions" => baker.getAllInteractions.toBakerResultResponseIO

      case GET -> Root / "interactions" / InteractionName(name) => baker.getInteraction(name).toBakerResultResponseIO

      case req@POST -> Root / "interactions" / "execute" =>
        for {
          executionRequest <- req.as[InteractionExecution.ExecutionRequest]
          result <-
            IO.fromFuture(IO(baker.executeSingleInteraction(executionRequest.id, executionRequest.ingredients)))
              .map(_.toSerializationInteractionExecutionResult)
              .toBakerResultResponseIO
        } yield result

      case req@POST -> Root / "recipes" =>
        for {
          encodedRecipe <- req.as[EncodedRecipe]
          recipe <- RecipeLoader.fromBytes(encodedRecipe.base64.getBytes(Charset.forName("UTF-8")))
          result <- baker.addRecipe(recipe, validate = true).toBakerResultResponseIO
        } yield result

      case GET -> Root / "recipes" => baker.getAllRecipes.toBakerResultResponseIO

      // This does not actually delete the recipe, but flags it as inactive, and it is idempotent
      case DELETE -> Root / "recipes" / RecipeId(recipeId) =>
        baker.getRecipe(recipeId).flatMap { recipeInformation =>
          baker.addRecipe(RecipeRecord.of(recipeInformation.compiledRecipe, updated = System.currentTimeMillis(), recipeInformation.validate, isActive = false))
        }(ExecutionContext.global).toBakerResultResponseIO

      case GET -> Root / "recipes" / RecipeId(recipeId) => baker.getRecipe(recipeId).toBakerResultResponseIO

      case GET -> Root / "recipes" / RecipeId(recipeId) / "visual" => baker.getRecipeVisual(recipeId).toBakerResultResponseIO
    })

  private def instance: HttpRoutes[IO] = Router("/instances" -> HttpRoutes.of[IO] {

    case GET -> Root => baker.getAllRecipeInstancesMetadata.toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) => baker.getRecipeInstanceState(recipeInstanceId).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "events" => baker.getEvents(recipeInstanceId).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "ingredient" / IngredientName(name) => baker.getIngredient(recipeInstanceId, name).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "ingredients" => baker.getIngredients(recipeInstanceId).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "visual" => baker.getVisualState(recipeInstanceId).toBakerResultResponseIO

    case POST -> Root / RecipeInstanceId(recipeInstanceId) / "bake" / RecipeId(recipeId) => baker.bake(recipeId, recipeInstanceId).toBakerResultResponseIO

    case DELETE -> Root / RecipeInstanceId(recipeInstanceId) / "delete" :? RemoveFromIndex(removeFromIndex) => baker.deleteRecipeInstance(recipeInstanceId, removeFromIndex.getOrElse(true)).toBakerResultResponseIO

    case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-when-received" :? CorrelationId(maybeCorrelationId) =>
      for {
        event <- req.as[EventInstance]
        result <- baker.fireEventAndResolveWhenReceived(recipeInstanceId, event, maybeCorrelationId).toBakerResultResponseIO
      } yield result

    case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-when-completed" :? CorrelationId(maybeCorrelationId) =>
      for {
        event <- req.as[EventInstance]
        result <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, maybeCorrelationId).toBakerResultResponseIO
      } yield result

    case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-on-event" / onEvent :? CorrelationId(maybeCorrelationId) =>
      for {
        event <- req.as[EventInstance]
        result <- baker.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, maybeCorrelationId).toBakerResultResponseIO
      } yield result

    case POST -> Root / RecipeInstanceId(recipeInstanceId) / "interaction" / InteractionName(interactionName) / "retry" =>
      for {
        result <- baker.retryInteraction(recipeInstanceId, interactionName).toBakerResultResponseIO
      } yield result

    case POST -> Root / RecipeInstanceId(recipeInstanceId) / "interaction" / InteractionName(interactionName) / "stop-retrying" =>
      for {
        result <- baker.stopRetryingInteraction(recipeInstanceId, interactionName).toBakerResultResponseIO
      } yield result

    case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "interaction" / InteractionName(interactionName) / "resolve" =>
      for {
        event <- req.as[EventInstance]
        result <- baker.resolveInteraction(recipeInstanceId, interactionName, event).toBakerResultResponseIO
      } yield result

    case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-sensory-event-and-await-received" :? CorrelationId(maybeCorrelationId) =>
      for {
        event <- req.as[EventInstance]
        result <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, event, maybeCorrelationId).toBakerResultResponseIO
      } yield result

    case POST -> Root / RecipeInstanceId(recipeInstanceId) / "await-event" / InteractionName(eventName) :? Timeout(timeoutMillis) =>
      val timeout = FiniteDuration(timeoutMillis, TimeUnit.MILLISECONDS)
      baker.awaitEvent(recipeInstanceId, eventName, timeout).toBakerResultResponseIO

    case POST -> Root / RecipeInstanceId(recipeInstanceId) / "await-completed" :? Timeout(timeoutMillis) =>
      val timeout = FiniteDuration(timeoutMillis, TimeUnit.MILLISECONDS)
      baker.awaitCompleted(recipeInstanceId, timeout).toBakerResultResponseIO

  })

  def metricsClassifier(apiUrlPrefix: String): Request[IO] => Option[String] = { request =>
    val uriPathRendered = request.uri.path.renderString
    val p = uriPathRendered.takeRight(uriPathRendered.length - apiUrlPrefix.length)

    if (p.startsWith("/app")) Some(p) // cardinality is low, we don't care
    else if (p.startsWith("/instances")) {
      val action = p.split('/') // /instances/<id>/<action>/... - we don't want ID here
      if (action.length >= 4) Some(s"/instances/${action(3)}") else Some("/instances/state")
    } else None
  }

  private implicit class BakerResultFutureHelper[A](f: => Future[A]) {
    def toBakerResultResponseIO(implicit encoder: Encoder[A]): IO[Response[IO]] =
      IO.fromFuture(IO(f)).toBakerResultResponseIO
  }
}
