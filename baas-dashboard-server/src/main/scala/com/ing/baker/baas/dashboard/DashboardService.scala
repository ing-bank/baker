package com.ing.baker.baas.dashboard

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import io.circe.generic.auto._
import io.circe.syntax._
import io.circe.{Encoder, Json, JsonObject}
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import org.http4s.server.blaze.BlazeServerBuilder
import com.ing.baker.baas.dashboard.DashboardService.commonEncode
import com.ing.baker.baas.dashboard.BakerEventEncoders._

object DashboardService {

  case class DashboardServiceComponents(serverAddress: InetSocketAddress, eventListenerAddress: InetSocketAddress)

  def commonEncode[A](a: A)(implicit encoder: Encoder[A]): Json =
    JsonObject("data" -> a.asJson).asJson

  def resource(dependencies: DashboardDependencies)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, DashboardServiceComponents] = {
    import dependencies._
    for {
      dashboard <- Dashboard.resource(stateNodeAddress, eventListenerAddress)
      dashboardService = new DashboardService(dashboard)
      server <- BlazeServerBuilder[IO]
        .bindSocketAddress(dashboardServiceAddress)
        .withHttpApp(dashboardService.build)
        .resource
    } yield DashboardServiceComponents(
      serverAddress = server.address,
      eventListenerAddress = dashboard.eventListenerLocalAddress
    )
  }
}

class DashboardService(bakeryApi: Dashboard)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/api/v3" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")

    case GET -> Root / "recipes" / recipeId / "instances" / recipeInstanceId / "events" =>
      for {
        data <- bakeryApi.listEvents(recipeId, recipeInstanceId)
        response <- Ok(commonEncode(data))
      } yield response

    case GET -> Root / "recipes" / recipeId / "instances" / recipeInstanceId =>
      for {
        data <- bakeryApi.getRecipeInstance(recipeId, recipeInstanceId)
        response <- Ok(commonEncode(data))
      } yield response

    case GET -> Root / "recipes" / recipeId / "instances" =>
      for {
        data <- bakeryApi.listInstances(recipeId)
        response <- Ok(commonEncode(data))
      } yield response

    case GET -> Root / "recipes" / recipeId =>
      for {
        data <- bakeryApi.getRecipe(recipeId)
        response <- Ok(commonEncode(data))
      } yield response

    case GET -> Root / "recipes" =>
      for {
        data <- bakeryApi.listRecipes
        response <- Ok(commonEncode(data))
      } yield response
  })
}
