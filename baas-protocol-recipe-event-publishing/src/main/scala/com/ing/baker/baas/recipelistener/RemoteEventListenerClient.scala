package com.ing.baker.baas.recipelistener

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.baas.recipelistener.BakeryHttp.Headers.`X-Bakery-Intent`
import com.ing.baker.baas.recipelistener.BakeryHttp.Headers.Intent
import com.ing.baker.baas.recipelistener.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import org.http4s.Method._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.{Status, Uri}

import scala.concurrent.ExecutionContext

object RemoteEventListenerClient {

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(hostname: Uri, pool: ExecutionContext)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, RemoteEventListenerClient] =
    BlazeClientBuilder[IO](pool)
      .resource
      .map(new RemoteEventListenerClient(_, hostname))
}

final class RemoteEventListenerClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def apply(recipeEventMetadata: RecipeEventMetadata, event: EventInstance): IO[Status] = {
    val request = POST(
      ProtocolDistributedEventPublishing.Event(recipeEventMetadata, event),
      hostname / "api" / "v3" / "recipe-event",
      `X-Bakery-Intent`(Intent.`Remote-Event-Listener`, hostname)
    )
    client.status(request)
  }
}
