package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}

import scala.concurrent.ExecutionContext

object BakeryControllerService {

  def resource(hostname: InetSocketAddress)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {
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

  def api: HttpRoutes[IO] = Router("/api/v3" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")
  })
}

