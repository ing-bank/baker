package com.ing.baker.baas.state

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.syntax.apply._
import com.ing.baker.baas.protocol.BaaSProto._
import com.ing.baker.baas.protocol.BaaSProtocol
import com.ing.baker.baas.protocol.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.runtime.akka.{EventSink, KafkaCachingEventSink}
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.Baker
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}

import scala.concurrent.Future

object StateNodeService {

  def resource(baker: Baker, eventSink: EventSink, recipeDirectory: String, hostname: InetSocketAddress)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Server[IO]] = {
    for {
      binding <- BlazeServerBuilder[IO]
        .bindSocketAddress(hostname)
        .withHttpApp(new StateNodeService(baker, eventSink, recipeDirectory).build)
        .resource
    } yield binding
  }
}

final class StateNodeService private(baker: Baker, eventSink: EventSink, recipeDirectory: String)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def loadRecipeIfNotFound[A](f: IO[A]): IO[A] =
    RecipeLoader.loadRecipesIfRecipeNotFound(recipeDirectory, baker)(f)

  def build: HttpApp[IO] =
    api.orNotFound

  def completeWithBakerFailures[A, R](result: IO[Future[A]])(f: A => R)(implicit decoder: EntityEncoder[IO, R]): IO[Response[IO]] =
    loadRecipeIfNotFound(IO.fromFuture(result)).attempt.flatMap {
      case Left(e: BakerException) => Ok(BaaSProtocol.BaaSRemoteFailure(e))
      case Left(e) => IO.raiseError(new IllegalStateException("No other exception but BakerExceptions should be thrown here.", e))
      case Right(a) => Ok(f(a))
    }

  def api: HttpRoutes[IO] = Router("/api/v3" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")

    case req@POST -> Root / "getRecipe" =>
      req.as[BaaSProtocol.GetRecipeRequest]
        .map(r => IO(baker.getRecipe(r.recipeId)))
        .flatMap(completeWithBakerFailures(_)(BaaSProtocol.GetRecipeResponse))

    case GET -> Root / "getAllRecipes" =>
      completeWithBakerFailures(RecipeLoader.loadRecipesIntoBaker(recipeDirectory, baker) *> IO(baker.getAllRecipes))(BaaSProtocol.GetAllRecipesResponse)

    case req@POST -> Root / "bake" =>
      req.as[BaaSProtocol.BakeRequest]
        .map(r => IO(baker.bake(r.recipeId, r.recipeInstanceId)))
        .flatMap(completeWithBakerFailures(_)(_ => ""))

    case req@POST -> Root / "fireEventAndResolveWhenReceived" =>
      req.as[BaaSProtocol.FireEventAndResolveWhenReceivedRequest]
        .map(request => IO(baker.fireEventAndResolveWhenReceived(request.recipeInstanceId, request.event, request.correlationId)))
        .flatMap(completeWithBakerFailures(_)(BaaSProtocol.FireEventAndResolveWhenReceivedResponse))

    case req@POST -> Root / "fireEventAndResolveWhenCompleted" =>
      req.as[BaaSProtocol.FireEventAndResolveWhenCompletedRequest]
        .map(request => IO(baker.fireEventAndResolveWhenCompleted(request.recipeInstanceId, request.event, request.correlationId)))
        .flatMap(completeWithBakerFailures(_)(BaaSProtocol.FireEventAndResolveWhenCompletedResponse))

    case req@POST -> Root / "fireEventAndResolveOnEvent" =>
      req.as[BaaSProtocol.FireEventAndResolveOnEventRequest]
        .map(request => IO(baker.fireEventAndResolveOnEvent(request.recipeInstanceId, request.event, request.onEvent, request.correlationId)))
        .flatMap(completeWithBakerFailures(_)(BaaSProtocol.FireEventAndResolveOnEventResponse))

    case POST -> Root / "fireEvent" =>
      Ok("") // TODO figure out what to do here with the 2 different futures

    case GET -> Root / "getAllRecipeInstancesMetadata" =>
      completeWithBakerFailures(IO(baker.getAllRecipeInstancesMetadata))(BaaSProtocol.GetAllRecipeInstancesMetadataResponse)

    case req@POST -> Root / "getRecipeInstanceState" =>
      req.as[BaaSProtocol.GetRecipeInstanceStateRequest]
        .map(request => IO(baker.getRecipeInstanceState(request.recipeInstanceId)))
        .flatMap(completeWithBakerFailures(_)(BaaSProtocol.GetRecipeInstanceStateResponse))

    case req@POST -> Root / "getVisualState" =>
      req.as[BaaSProtocol.GetVisualStateRequest]
        .map(request => IO(baker.getVisualState(request.recipeInstanceId)))
        .flatMap(completeWithBakerFailures(_)(BaaSProtocol.GetVisualStateResponse))

    case req@POST -> Root / "retryInteraction" =>
      req.as[BaaSProtocol.RetryInteractionRequest]
        .map(request => IO(baker.retryInteraction(request.recipeInstanceId, request.interactionName)))
        .flatMap(completeWithBakerFailures(_)(_ => ""))

    case req@POST -> Root / "resolveInteraction" =>
      req.as[BaaSProtocol.ResolveInteractionRequest]
        .map(request => IO(baker.resolveInteraction(request.recipeInstanceId, request.interactionName, request.event)))
        .flatMap(completeWithBakerFailures(_)(_ => ""))

    case req@POST -> Root / "stopRetryingInteraction" =>
      req.as[BaaSProtocol.StopRetryingInteractionRequest]
        .map(request => IO(baker.stopRetryingInteraction(request.recipeInstanceId, request.interactionName)))
        .flatMap(completeWithBakerFailures(_)(_ => ""))

    case _@GET -> Root / "events" =>
      Ok(eventSink.lastEvents.toString)
  })
}
