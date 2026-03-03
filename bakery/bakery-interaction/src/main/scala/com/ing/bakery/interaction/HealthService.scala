package com.ing.bakery.interaction

import cats.effect.{IO, Resource}
import org.http4s.blaze.server._
import org.http4s.dsl.io.{->, /, GET, Ok, Root, _}
import org.http4s.implicits._
import org.http4s.server.{Router, Server}
import org.http4s.{HttpApp, HttpRoutes}

import java.net.InetSocketAddress
import scala.concurrent.ExecutionContext

object HealthService {

  def resource(address: InetSocketAddress): Resource[IO, Server] =
    BlazeServerBuilder[IO](ExecutionContext.global)
      .bindSocketAddress(address)
      .withHttpApp(new HealthService().build)
      .resource
}

final class HealthService {

  def build: HttpApp[IO] =
    health.orNotFound

  def health: HttpRoutes[IO] = Router("/" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")
  })
}
