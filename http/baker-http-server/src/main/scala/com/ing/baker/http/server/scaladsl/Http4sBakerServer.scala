package com.ing.baker.http.server.scaladsl

import cats.data.OptionT
import cats.effect.{Blocker, ContextShift, IO, Resource, Sync, Timer}
import cats.implicits._
import com.ing.baker.http.server.common.RecipeLoader
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{Baker, BakerResult, EncodedRecipe, EventInstance}
import com.ing.baker.runtime.serialization.InteractionExecution
import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.typesafe.scalalogging.LazyLogging
import io.circe._
import io.circe.generic.auto._
import io.prometheus.client.CollectorRegistry
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.middleware.{CORS, Logger, Metrics}
import org.http4s.server.{Router, Server}
import org.slf4j.LoggerFactory

import java.io.File
import java.net.InetSocketAddress
import java.nio.charset.Charset
import scala.concurrent.duration.DurationInt
import scala.concurrent.{ExecutionContext, Future}

object Http4sBakerServer {

  def resource(baker: Baker, ec: ExecutionContext, hostname: InetSocketAddress, apiUrlPrefix: String, dashboardPath: String, loggingEnabled: Boolean)
              (implicit sync: Sync[IO], cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Server[IO]] = {

    val bakeryRequestClassifier: Request[IO] => Option[String] = { request =>
      val uriPath = request.uri.path
      val p = uriPath.takeRight(uriPath.length - apiUrlPrefix.length)

      if (p.startsWith("/app")) Some(p) // cardinality is low, we don't care
      else if (p.startsWith("/instances")) {
        val action = p.split('/') // /instances/<id>/<action>/... - we don't want ID here
        if (action.length >= 4) Some(s"/instances/${action(3)}") else Some("/instances/state")
      } else None
    }

    val apiLoggingAction: Option[String => IO[Unit]] = if (loggingEnabled) {
      val apiLogger = LoggerFactory.getLogger("API")
      Some(s => IO(apiLogger.info(s)))
    } else None

    for {
      metrics <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_api")
      blocker <- Blocker[IO]
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
                logAction = apiLoggingAction) {

                def dashboardFile(request: Request[IO], filename: String): OptionT[IO, Response[IO]] =
                  StaticFile.fromFile(new File(dashboardPath + "/" + filename), blocker, Some(request))

                def index(request: Request[IO]) = dashboardFile(request, "index.html").getOrElseF(NotFound())

                Router(
                  apiUrlPrefix -> Metrics[IO](metrics, classifierF = bakeryRequestClassifier)(routes(baker)),
                  "/" -> HttpRoutes.of[IO] {
                    case request =>
                      if (dashboardPath.isEmpty) NotFound()
                      else dashboardFile(request, request.pathInfo).getOrElseF(index(request))
                  }
                ) orNotFound
              })).resource
    } yield server
  }

  def routes(baker: Baker)(implicit cs: ContextShift[IO], timer: Timer[IO]): HttpRoutes[IO] =
    new Http4sBakerServer(baker).routes
}

final class Http4sBakerServer private(baker: Baker)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends LazyLogging {

  object CorrelationId extends OptionalQueryParamDecoderMatcher[String]("correlationId")

  private class RegExpValidator(regexp: String) {
    def unapply(str: String): Option[String] = if (str.matches(regexp)) Some(str) else None
  }

  private object RecipeId extends RegExpValidator("[A-Za-z0-9]+")

  private object RecipeInstanceId extends RegExpValidator("[A-Za-z0-9-]+")

  private object InteractionName extends RegExpValidator("[A-Za-z0-9_]+")

  implicit val recipeDecoder: EntityDecoder[IO, EncodedRecipe] = jsonOf[IO, EncodedRecipe]

  implicit val eventInstanceDecoder: EntityDecoder[IO, EventInstance] = jsonOf[IO, EventInstance]
  implicit val interactionExecutionRequestDecoder: EntityDecoder[IO, InteractionExecution.ExecutionRequest] = jsonOf[IO, InteractionExecution.ExecutionRequest]
  implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]

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

      case GET -> Root / "recipes" / RecipeId(recipeId) => baker.getRecipe(recipeId).toBakerResultResponseIO

      case GET -> Root / "recipes" / RecipeId(recipeId) / "visual" => baker.getRecipeVisual(recipeId).toBakerResultResponseIO
    })

  private def instance: HttpRoutes[IO] = Router("/instances" -> HttpRoutes.of[IO] {

    case GET -> Root => baker.getAllRecipeInstancesMetadata.toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) => baker.getRecipeInstanceState(recipeInstanceId).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "events" => baker.getEvents(recipeInstanceId).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "ingredients" => baker.getIngredients(recipeInstanceId).toBakerResultResponseIO

    case GET -> Root / RecipeInstanceId(recipeInstanceId) / "visual" => baker.getVisualState(recipeInstanceId).toBakerResultResponseIO

    case POST -> Root / RecipeInstanceId(recipeInstanceId) / "bake" / RecipeId(recipeId) => baker.bake(recipeId, recipeInstanceId).toBakerResultResponseIO

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
  })


  private implicit class BakerResultFutureHelper[A](f: => Future[A]) {
    def toBakerResultResponseIO(implicit encoder: Encoder[A]): IO[Response[IO]] =
      IO.fromFuture(IO(f)).toBakerResultResponseIO
  }

  private implicit class BakerResultIOHelper[A](io: => IO[A]) {
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
