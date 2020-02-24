package com.ing.baker.baas.smoke

import cats.effect.{ContextShift, IO, Resource, Timer}
import org.http4s.{Status, Uri}
import org.http4s.client.Client

class EventListenerClient(client: Resource[IO, Client[IO]], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def ping: IO[Status] =
    client.use(_.statusFromUri(hostname / "api"))

  def events: IO[List[String]] =
    client.use(_.expect[String](hostname / "api" / "events")).map(_.split(", ").toList)
}
