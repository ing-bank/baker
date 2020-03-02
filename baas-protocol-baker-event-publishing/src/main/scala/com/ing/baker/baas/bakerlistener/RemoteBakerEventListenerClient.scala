package com.ing.baker.baas.bakerlistener

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.bakerlistener.BakeryHttp.Headers.{Intent, `X-Bakery-Intent`}
import com.ing.baker.baas.bakerlistener.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.runtime.scaladsl.BakerEvent
import org.http4s.Method._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.{Status, Uri}

import scala.concurrent.ExecutionContext

object RemoteBakerEventListenerClient {

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(hostname: Uri, pool: ExecutionContext)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, RemoteBakerEventListenerClient] =
    BlazeClientBuilder[IO](pool)
      .resource
      .map(new RemoteBakerEventListenerClient(_, hostname))
}

final class RemoteBakerEventListenerClient(client: Client[IO], hostname: Uri) {

  def fireEvent(event: BakerEvent): IO[Status] = {
    val request = POST(
      event,
      hostname / "api" / "v3" / "baker-event",
      `X-Bakery-Intent`(Intent.`Remote-Event-Listener`, hostname)
    )
    client.status(request)
  }
}
