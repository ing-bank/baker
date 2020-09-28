package com.ing.bakery.baker

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{Baker, BakerResult, EventInstance}
import io.circe._
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.typesafe.scalalogging.LazyLogging
import org.http4s.server.middleware.Logger
import org.slf4j.LoggerFactory

import scala.concurrent.{ExecutionContext, Future}
import scala.util.Try

object BakerService  {

  def resource(baker: Baker, hostname: InetSocketAddress, serviceDiscovery: ServiceDiscovery, loggingEnabled: Boolean)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {
    val apiLoggingAction: Option[String => IO[Unit]] = if (loggingEnabled) {
      val apiLogger = LoggerFactory.getLogger("API")
      Some(s => IO(apiLogger.info(s)))
    } else None
    for {
      binding <- BlazeServerBuilder[IO](ec)
        .bindSocketAddress(hostname)
        .withHttpApp(
          Logger.httpApp(
            logHeaders = loggingEnabled,
            logBody = loggingEnabled,
            logAction = apiLoggingAction)
          (new BakerService(baker, serviceDiscovery).build)
        ).resource
    } yield binding
  }
}

final class BakerService private(baker: Baker, serviceDiscovery: ServiceDiscovery)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends LazyLogging {

  object CorrelationId extends OptionalQueryParamDecoderMatcher[String]("correlationId")

  private class RegExpValidator(regexp: String) {
    def unapply(str: String): Option[String] = if (str.matches(regexp)) Some(str) else None
  }
  private object RecipeId extends RegExpValidator("[A-Za-z0-9]+")
  private object RecipeInstanceId extends RegExpValidator("[A-Za-z0-9-]+")
  private object InteractionName extends RegExpValidator("[A-Za-z0-9_]+")

  implicit val eventInstanceDecoder: EntityDecoder[IO, EventInstance] = jsonOf[IO, EventInstance]
  implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]

  def build: HttpApp[IO] = Router("/api/bakery" -> (app <+> instance)) orNotFound

  private def callBaker[A](f : => Future[A])(implicit encoder: Encoder[A]): IO[Response[IO]] = {
    IO.fromFuture(IO(f)).attempt.flatMap {
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

        case GET -> Root / "interactions" => for {
          interactions <- serviceDiscovery.get
          resp <- Ok(interactions.map(_.name).asJson)
        } yield  resp

        case GET -> Root / "recipes" => callBaker(baker.getAllRecipes)

        case GET -> Root / "recipes" / RecipeId(recipeId) => callBaker(baker.getRecipe(recipeId))
    } )

  private def instance: HttpRoutes[IO]  = Router("/instances" ->  HttpRoutes.of[IO] {

      case GET -> Root => callBaker(baker.getAllRecipeInstancesMetadata)

      case GET -> Root / RecipeInstanceId(recipeInstanceId)  => callBaker(baker.getRecipeInstanceState(recipeInstanceId))

      case GET -> Root / RecipeInstanceId(recipeInstanceId) / "events" => callBaker(baker.getEvents(recipeInstanceId))

      case GET -> Root / RecipeInstanceId(recipeInstanceId) / "ingredients" => callBaker(baker.getIngredients(recipeInstanceId))

      case GET -> Root / RecipeInstanceId(recipeInstanceId) / "visual" => callBaker(baker.getVisualState(recipeInstanceId))

      case POST -> Root / RecipeInstanceId(recipeInstanceId) / "bake"  / RecipeId(recipeId) => callBaker(baker.bake(recipeId, recipeInstanceId))

      case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-when-received" :? CorrelationId(maybeCorrelationId)  =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveWhenReceived(recipeInstanceId, event, maybeCorrelationId))
        } yield result

      case req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-when-completed" :? CorrelationId(maybeCorrelationId)  =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, maybeCorrelationId))
        } yield result

      case  req@POST -> Root / RecipeInstanceId(recipeInstanceId) / "fire-and-resolve-on-event" / onEvent :? CorrelationId(maybeCorrelationId) =>
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
