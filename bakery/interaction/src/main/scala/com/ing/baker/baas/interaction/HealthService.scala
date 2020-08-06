package com.ing.baker.baas.interaction

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.{HttpApp, HttpRoutes}
import org.http4s.dsl.io.{->, /, GET, Ok, Root}
import org.http4s.server.{Router, Server}
import org.http4s.server.blaze._

import scala.concurrent.ExecutionContext

object HealthService {

  def resource(address: InetSocketAddress)(implicit cs: ContextShift[IO], clock: Timer[IO]): Resource[IO, Server[IO]] =
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
