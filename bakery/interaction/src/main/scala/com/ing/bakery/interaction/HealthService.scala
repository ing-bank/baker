package com.ing.bakery.interaction

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import org.http4s.dsl.io.{->, /, GET, Ok, Root, _}
import org.http4s.implicits._
import org.http4s.server.blaze._
import org.http4s.server.{Router, Server}
import org.http4s.{HttpApp, HttpRoutes}

import scala.concurrent.ExecutionContext
import cats.effect.Temporal

object HealthService {

  def resource(address: InetSocketAddress)(implicit clock: Temporal[IO]): Resource[IO, Server[IO]] =
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
