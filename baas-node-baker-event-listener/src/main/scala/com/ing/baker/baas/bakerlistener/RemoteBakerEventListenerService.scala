package com.ing.baker.baas.bakerlistener

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.baas.bakerlistener.BakeryHttp.ProtoEntityEncoders._
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}

object RemoteBakerEventListenerService {

  def resource(listenerFunction: BakerEvent => Unit, address: InetSocketAddress)(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] =
    BlazeServerBuilder[IO]
      .bindSocketAddress(address)
      .withHttpApp(new RemoteBakerEventListenerService(listenerFunction).build)
      .resource
}

final class RemoteBakerEventListenerService(listenerFunction: BakerEvent => Unit) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/api/v3" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")

    case req@POST -> Root / "baker-event" =>
      for {
        event <- req.as[BakerEvent]
        _ <- IO.pure(IO(listenerFunction(event)).unsafeRunAsyncAndForget())
        response <- Ok()
      } yield response
  })
}
