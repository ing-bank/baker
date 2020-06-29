package com.ing.baker.baas.state

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, SensoryEventResult}
import io.circe._
import io.circe.generic.auto._
import io.circe.generic.semiauto._
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}
import com.ing.baker.runtime.serialization.EventJsonEncoders._
import com.ing.baker.runtime.serialization.EventJsonToScalaDslDecoders._

object StateNodeService {

  def resource(baker: Baker, recipeDirectory: String, hostname: InetSocketAddress, serviceDiscovery: ServiceDiscovery)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Server[IO]] = {
    for {
      binding <- BlazeServerBuilder[IO]
        .bindSocketAddress(hostname)
        .withHttpApp(new StateNodeService(baker, recipeDirectory, serviceDiscovery).build)
        .resource
    } yield binding
  }
}

final class StateNodeService private(baker: Baker, recipeDirectory: String, serviceDiscovery: ServiceDiscovery)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def build: HttpApp[IO] = Router("/api/bakery" -> (app <+> instance)) orNotFound

  implicit val eventInstanceDecoder: EntityDecoder[IO, EventInstance] = jsonOf[IO, EventInstance]
  implicit val sensoryEventStatusEncoder: Encoder[SensoryEventStatus] =
      (status: SensoryEventStatus) => Json.obj(("status" -> status.toString.asJson))

  implicit val sensoryEventResultEncoder: Encoder[SensoryEventResult] = deriveEncoder[SensoryEventResult]

  private def app: HttpRoutes[IO] = Router("/app" ->
    HttpRoutes.of[IO] {
        case GET -> Root / "health" =>
          Ok("Ok")

        case GET -> Root / "interactions" => for {
          interactions <- serviceDiscovery.get
          resp <- Ok(interactions.map(_.name).asJson)
        } yield  resp

        case GET -> Root / "recipes" => for {
          recipes <-  IO.fromFuture(IO(baker.getAllRecipes))
          resp <- Ok(recipes.asJson)
        } yield resp

    } )

  private def instance: HttpRoutes[IO]  = Router("/instance" ->
    HttpRoutes.of[IO] {
      case GET -> Root / recipeInstanceId  => for {
        state <- IO.fromFuture(IO(baker.getRecipeInstanceState(recipeInstanceId)))
        resp <- Ok(state.asJson)
      } yield resp

      case GET -> Root / recipeInstanceId / "events" => for {
        events <- IO.fromFuture(IO(baker.getEvents(recipeInstanceId)))
        resp <- Ok(events.map(_.name).asJson)
      } yield resp

      case GET -> Root / recipeInstanceId / "ingredients" => for {
        ingredients <- IO.fromFuture(IO(baker.getIngredients(recipeInstanceId)))
        resp <- Ok(ingredients.keys.asJson)
      } yield resp

      case GET -> Root / recipeInstanceId / "visual" => for {
        visualState <- IO.fromFuture(IO(baker.getVisualState(recipeInstanceId)))
        resp <- Ok(Map("state" -> visualState).asJson)
      } yield resp

      case POST -> Root / recipeInstanceId / "bake"  / recipeId => for {
          _ <- IO(baker.bake(recipeId, recipeInstanceId))
          resp <- Ok()
        } yield resp

      case req@POST -> Root / recipeInstanceId / "fire" / correlationId / "resolveWhenReceived"   =>
        for {
          event <- req.as[EventInstance]
          status <- IO.fromFuture(IO(baker.fireEventAndResolveWhenReceived(recipeInstanceId, event, recipeInstanceId)))
          resp <- Ok(status.asJson)
        } yield resp

      case req@POST -> Root / recipeInstanceId / "fire" / correlationId / "resolveWhenCompleted"   =>
        for {
          event <- req.as[EventInstance]
          result <- IO.fromFuture(IO(baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, recipeInstanceId)))
          resp <- Ok(result.asJson)
        } yield resp

    })

}
