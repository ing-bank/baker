package com.ing.baker.baas.recipelistener

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.{Router, Server}
import com.ing.baker.baas.protocol
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.recipelistener.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import org.http4s.server.blaze.BlazeServerBuilder

object RemoteEventListenerService {

  def resource(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit, address: InetSocketAddress)(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] =
    BlazeServerBuilder[IO]
      .bindSocketAddress(address)
      .withHttpApp(new RemoteEventListenerService(listenerFunction).build)
      .resource
}

final class RemoteEventListenerService(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/api/v3" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")

    case req@POST -> Root / "recipe-event" =>
      for {
        event <- req.as[protocol.ProtocolDistributedEventPublishing.Event]
        _ <- IO.pure(IO(listenerFunction(event.recipeEventMetadata, event.event)).unsafeRunAsyncAndForget())
        response <- Ok()
      } yield response
  })
}
