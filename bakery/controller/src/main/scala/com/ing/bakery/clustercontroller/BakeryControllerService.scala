package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}

import scala.concurrent.ExecutionContext
import cats.effect.Temporal

object BakeryControllerService {

  def resource(hostname: InetSocketAddress)(implicit timer: Temporal[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {
    for {
      binding <- BlazeServerBuilder[IO](ec)
        .bindSocketAddress(hostname)
        .withHttpApp(new BakeryControllerService().build)
        .resource
    } yield binding
  }
}

final class BakeryControllerService(implicit cs: ContextShift[IO]) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/api/bakery" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")
  })
}

