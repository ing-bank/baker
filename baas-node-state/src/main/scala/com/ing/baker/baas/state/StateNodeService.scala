package com.ing.baker.baas.state

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

import scala.concurrent.Future

object StateNodeService {

  def resource(baker: Baker, recipeDirectory: String, hostname: InetSocketAddress, serviceDiscovery: ServiceDiscovery)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Server[IO]] = {
    for {
      binding <- BlazeServerBuilder[IO]
        .bindSocketAddress(hostname)
        .withHttpApp(new StateNodeService(baker, serviceDiscovery).build)
        .resource
    } yield binding
  }
}

final class StateNodeService private(baker: Baker, serviceDiscovery: ServiceDiscovery)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  object CorrelationId extends OptionalQueryParamDecoderMatcher[String]("correlationId")

  implicit val eventInstanceDecoder: EntityDecoder[IO, EventInstance] = jsonOf[IO, EventInstance]
  implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]

  def build: HttpApp[IO] = Router("/api/bakery" -> (app <+> instance)) orNotFound

  private def callBaker[A](f : => Future[A])(implicit encoder: Encoder[A]): IO[Response[IO]] = {
    IO.fromFuture(IO(f)).attempt.flatMap {
      case Left(e: BakerException) => Ok(BakerResult(e))
      case Left(e) => InternalServerError(s"No other exception but BakerExceptions should be thrown here: ${e.getCause}")
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

        case GET -> Root / "recipes" / recipeId => callBaker(baker.getRecipe(recipeId))
    } )

  private def instance: HttpRoutes[IO]  = Router("/instances" ->  HttpRoutes.of[IO] {

      case GET -> Root => callBaker(baker.getAllRecipeInstancesMetadata)

      case GET -> Root / recipeInstanceId  => callBaker(baker.getRecipeInstanceState(recipeInstanceId))

      case GET -> Root / recipeInstanceId / "events" => callBaker(baker.getEvents(recipeInstanceId))

      case GET -> Root / recipeInstanceId / "ingredients" => callBaker(baker.getIngredients(recipeInstanceId))

      case GET -> Root / recipeInstanceId / "visual" => callBaker(baker.getVisualState(recipeInstanceId))

      case POST -> Root / recipeInstanceId / "bake"  / recipeId => callBaker(baker.bake(recipeId, recipeInstanceId))

      case req@POST -> Root / recipeInstanceId / "fireAndResolveWhenReceived" :? CorrelationId(maybeCorrelationId)  =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveWhenReceived(recipeInstanceId, event, maybeCorrelationId))
        } yield result

      case req@POST -> Root / recipeInstanceId / "fireAndResolveWhenCompleted" :? CorrelationId(maybeCorrelationId)  =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, maybeCorrelationId))
        } yield result

      case  req@POST -> Root / recipeInstanceId / "fireAndResolveOnEvent" / onEvent :? CorrelationId(maybeCorrelationId) =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, maybeCorrelationId))
        } yield result

      case POST -> Root / recipeInstanceId / "retryInteraction" / interactionName =>
        for {
          result <- callBaker(baker.retryInteraction(recipeInstanceId, interactionName))
        } yield result

      case POST -> Root / recipeInstanceId / "stopRetryingInteraction" / interactionName =>
        for {
          result <- callBaker(baker.stopRetryingInteraction(recipeInstanceId, interactionName))
        } yield result

      case req@POST -> Root / recipeInstanceId / "resolveInteraction" / interactionName =>
        for {
          event <- req.as[EventInstance]
          result <- callBaker(baker.resolveInteraction(recipeInstanceId, interactionName, event))
        } yield result
    })

}
