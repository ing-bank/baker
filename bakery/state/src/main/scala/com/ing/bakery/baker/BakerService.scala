package com.ing.bakery.baker

import cats.data.OptionT
import cats.effect.{IO, Resource, Sync}
import cats.implicits._
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.scaladsl.{Baker, BakerResult, EventInstance}
import com.ing.baker.runtime.serialization.InteractionExecution
import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.typesafe.scalalogging.LazyLogging
import io.circe._
import io.circe.generic.auto._
import io.prometheus.client.CollectorRegistry
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.runtime.serialization.JsonDecoders._
import io.prometheus.client.CollectorRegistry
import org.http4s.server.staticcontent._
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.middleware.{CORS, CORSConfig, Logger, Metrics}
import org.http4s.server.{Router, Server}
import org.slf4j.LoggerFactory

import java.io.File
import java.net.InetSocketAddress
import scala.concurrent.duration.DurationInt
import scala.concurrent.{ExecutionContext, Future}
import cats.effect.Temporal

object BakerService {

  def resource(baker: Baker, hostname: InetSocketAddress, apiUrlPrefix: String, dashboardPath: String, interactions: InteractionManager[IO], loggingEnabled: Boolean)
              (implicit sync: Sync[IO], timer: Temporal[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {

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
      blocker <- Resource.unit[IO]
      server <- BlazeServerBuilder[IO](ec)
        .bindSocketAddress(hostname)
        .withHttpApp(
          CORS(
          Logger.httpApp(
            logHeaders = loggingEnabled,
            logBody = loggingEnabled,
            logAction = apiLoggingAction) {

             def dashboardFile(request: Request[IO], filename: String): OptionT[IO, Response[IO]] =
                StaticFile.fromFile(new File(dashboardPath + "/" + filename), blocker, Some(request))

             def index(request: Request[IO]) = dashboardFile(request, "index.html").getOrElseF(NotFound())

              Router(
                apiUrlPrefix -> Metrics[IO](metrics, classifierF = bakeryRequestClassifier)(routes(baker, interactions)),
                "/" -> HttpRoutes.of[IO] {
                  case request =>
                    if (dashboardPath.isEmpty) NotFound()
                    else dashboardFile(request, request.pathInfo).getOrElseF(index(request))
                }
              ) orNotFound
            }, CORSConfig(
            anyOrigin = true,
            allowCredentials = true, maxAge = 1.day.toSeconds))).resource
          } yield server
    }

    def routes(baker: Baker, interactionManager: InteractionManager[IO])(implicit timer: Temporal[IO]): HttpRoutes[IO] =
      new BakerService(baker, interactionManager).routes
  }

  final class BakerService private(baker: Baker, interactionManager: InteractionManager[IO])(implicit cs: ContextShift[IO], timer: Temporal[IO]) extends LazyLogging {

    object CorrelationId extends OptionalQueryParamDecoderMatcher[String]("correlationId")

    private class RegExpValidator(regexp: String) {
      def unapply(str: String): Option[String] = if (str.matches(regexp)) Some(str) else None
    }

    private object RecipeId extends RegExpValidator("[A-Za-z0-9]+")

    private object RecipeInstanceId extends RegExpValidator("[A-Za-z0-9-]+")

    private object InteractionName extends RegExpValidator("[A-Za-z0-9_]+")

    implicit val eventInstanceDecoder: EntityDecoder[IO, EventInstance] = jsonOf[IO, EventInstance]
    implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]
    implicit val interactionEntityEncoder: EntityEncoder[IO, InteractionExecution.Descriptor] = jsonEncoderOf[IO, InteractionExecution.Descriptor]

    def routes: HttpRoutes[IO] = app <+> instance

    private def callBaker[A](f: => Future[A])(implicit encoder: Encoder[A]): IO[Response[IO]] = {
      IO.fromFuture(IO(f)).attempt.flatMap {
        case Left(e: NoSuchProcessException) => NotFound(BakerResult(e))
        case Left(e: BakerException) => Ok(BakerResult(e))
        case Left(e) =>
          logger.error(s"Unexpected exception happened when calling Baker", e)
          InternalServerError(s"No other exception but BakerExceptions should be thrown here: ${e.getCause}")
        case Right(Unit) => Ok(BakerResult.Ack)
        case Right(a) => Ok(BakerResult(a))
      }
    }

    private def app: HttpRoutes[IO] = Router("/app" ->
      HttpRoutes.of[IO] {
        case GET -> Root / "health" => Ok()

        case GET -> Root / "interactions" => callBaker(baker.getAllInteractions)

        case GET -> Root / "interactions" / InteractionName(name) => callBaker(baker.getInteraction(name))

        case GET -> Root / "recipes" => callBaker(baker.getAllRecipes)

        case GET -> Root / "recipes" / RecipeId(recipeId) => callBaker(baker.getRecipe(recipeId))

        case GET -> Root / "recipes" / RecipeId(recipeId) / "visual" => callBaker(baker.getRecipeVisual(recipeId))
      })

    private def instance: HttpRoutes[IO] = Router("/instances" -> HttpRoutes.of[IO] {

      case GET -> Root => callBaker(baker.getAllRecipeInstancesMetadata)

      case GET -> Root / RecipeInstanceId(recipeInstanceId) => callBaker(baker.getRecipeInstanceState(recipeInstanceId))

      case GET -> Root / RecipeInstanceId(recipeInstanceId) / "events" => callBaker(baker.getEvents(recipeInstanceId))

      case GET -> Root / RecipeInstanceId(recipeInstanceId) / "ingredients" => callBaker(baker.getIngredients(recipeInstanceId))

      case GET -> Root / RecipeInstanceId(recipeInstanceId) / "visual" => callBaker(baker.getVisualState(recipeInstanceId))

      case POST -> Root / RecipeInstanceId(recipeInstanceId) / "bake" / RecipeId(recipeId) => callBaker(baker.bake(recipeId, recipeInstanceId))

      case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-when-received" :? CorrelationId(maybeCorrelationId) =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveWhenReceived(recipeInstanceId, event, maybeCorrelationId))
        } yield result

      case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-when-completed" :? CorrelationId(maybeCorrelationId) =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, maybeCorrelationId))
        } yield result

      case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-on-event" / onEvent :? CorrelationId(maybeCorrelationId) =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, maybeCorrelationId))
        } yield result

      case POST -> Root / RecipeInstanceId(recipeInstanceId) / "interaction" / InteractionName(interactionName) / "retry" =>
        for {
          result <- callBaker(baker.retryInteraction(recipeInstanceId, interactionName))
        } yield result

      case POST -> Root / RecipeInstanceId(recipeInstanceId) / "interaction" / InteractionName(interactionName) / "stop-retrying" =>
        for {
          result <- callBaker(baker.stopRetryingInteraction(recipeInstanceId, interactionName))
        } yield result

      case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "interaction" / InteractionName(interactionName) / "resolve" =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.resolveInteraction(recipeInstanceId, interactionName, event))
        } yield result
    })

  }
