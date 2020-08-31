package com.ing.bakery.smoke

import cats.effect.{ContextShift, IO, Timer}
import org.http4s.client.Client
import org.http4s.{Status, Uri}

class EventListenerClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def ping: IO[Status] =
    client.statusFromUri(hostname / "api")

  def events: IO[List[String]] =
    client.expect[String](hostname / "api" / "events").map(_.split(", ").toList)
}
