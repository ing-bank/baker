package com.ing.bakery.testing

import java.net.InetSocketAddress

import cats.effect.concurrent.{MVar, MVar2}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.smoke.printYellow
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import org.http4s.server.blaze.BlazeServerBuilder

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

object HoldCleanup {

  def resource(hostname: InetSocketAddress)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Unit] =
    for {
      lock <- Resource.liftF(MVar.empty[IO, Unit])
      _ <- BlazeServerBuilder[IO](ec)
        .bindSocketAddress(hostname)
        .withHttpApp(new HoldCleanup(lock).build)
        .resource
      _ <- Resource.liftF(printYellow(s"To terminate the tests, please visit http://localhost:${hostname.getPort}/"))
      _ <- Resource.liftF(lock.take *> IO.sleep(1.seconds))
    } yield ()
}

final class HoldCleanup private(lock: MVar2[IO, Unit])(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/" -> HttpRoutes.of[IO] {

    case GET -> Root =>
      for {
        _ <- lock.put(())
        response <- Ok(s"Terminating tests now...")
      } yield response
  })
}
