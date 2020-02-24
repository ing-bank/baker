package com.ing.baker.baas.recipelistener

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.baas.recipelistener.BakeryHttp.Headers.`X-Bakery-Intent`
import com.ing.baker.baas.recipelistener.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import org.http4s.Method._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.dsl.io._

class RemoteEventListenerClient(client: Resource[IO, Client[IO]], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def apply(recipeEventMetadata: RecipeEventMetadata, event: EventInstance): IO[Unit] = {
    val request = POST(
      ProtocolDistributedEventPublishing.Event(recipeEventMetadata, event),
      hostname / "api" / "v3" / "apply",
      `X-Bakery-Intent`(hostname)
    )
    client.use(_.status(request)).void
  }

}
