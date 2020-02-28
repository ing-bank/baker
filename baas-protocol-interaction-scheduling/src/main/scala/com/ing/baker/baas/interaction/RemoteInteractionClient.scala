package com.ing.baker.baas.interaction

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.interaction.BakeryHttp.Headers.{Intent, `X-Bakery-Intent`}
import com.ing.baker.baas.interaction.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.types.Type
import org.http4s.Method._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._

import scala.concurrent.ExecutionContext

object RemoteInteractionClient {

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(hostname: Uri, pool: ExecutionContext)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, RemoteInteractionClient] =
    BlazeClientBuilder[IO](pool)
      .resource
      .map(new RemoteInteractionClient(_, hostname))
}

final class RemoteInteractionClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def interface: IO[(String, Seq[Type])] = {
    val request = GET(
      hostname / "api" / "v3" / "interface",
      `X-Bakery-Intent`(Intent.`Remote-Interaction`, hostname)
    )
    client.expect[ProtocolInteractionExecution.InstanceInterface](request)
      .map(message => (message.name, message.input))
  }

  def runInteraction(input: Seq[IngredientInstance]): IO[Option[EventInstance]] = {
    val request = POST(
      ProtocolInteractionExecution.ExecuteInstance(input),
      hostname / "api" / "v3" / "run-interaction",
      `X-Bakery-Intent`(Intent.`Remote-Interaction`, hostname)
    )
    client.expect[Either[
      ProtocolInteractionExecution.InstanceExecutedSuccessfully,
      ProtocolInteractionExecution.InstanceExecutionFailed]](request)
      .flatMap {
      case Left(result) =>
        IO.pure(result.result)
      case Right(e) =>
        IO.raiseError(new RuntimeException(s"Remote interaction failed with message: ${e.message}"))
    }
  }
}
