package com.ing.baker.baas.interaction

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.interaction.BakeryHttp.Headers.{Intent, `X-Bakery-Intent`}
import com.ing.baker.baas.interaction.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.baas.interaction.RemoteInteractionClient.InteractionEndpoint
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceInterface
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.types.Type
import org.http4s.Method._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._

import scala.concurrent.ExecutionContext
import scala.util.Try

object RemoteInteractionClient {

  case class InteractionEndpoint(id: String, name: String, interface: Seq[Type])

  object InteractionEndpoint {

    def toBase64(xs: List[InteractionEndpoint]): String =
      ProtoMap.encode64(ProtocolInteractionExecution.Interfaces(xs.map(a => InstanceInterface(id = a.id, name = a.name, input = a.interface))))

    def fromBase64(str: String): Try[List[InteractionEndpoint]] =
      ProtoMap.decode64(str)(interfacesProto).map(_.interfaces.map(i => InteractionEndpoint(id = i.id, name = i.name, interface = i.input)))
  }

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(hostname: Uri, pool: ExecutionContext, tlsConfig: Option[BakeryHttp.TLSConfig])(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, RemoteInteractionClient] =
    BlazeClientBuilder[IO](pool, tlsConfig.map(BakeryHttp.loadSSLContext))
      .withCheckEndpointAuthentication(false)
      .resource
      .map(new RemoteInteractionClient(_, hostname))
}

final class RemoteInteractionClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def interface: IO[List[InteractionEndpoint]] = {
    val request = GET(
      hostname / "api" / "v3" / "interaction",
      `X-Bakery-Intent`(Intent.`Remote-Interaction`, hostname)
    )
    client.expect[ProtocolInteractionExecution.Interfaces](request)
      .map(_.interfaces.map(message => InteractionEndpoint(message.id, message.name, message.input)))
  }

  def runInteraction(interactionId: String, input: Seq[IngredientInstance]): IO[Option[EventInstance]] = {
    val request = POST(
      ProtocolInteractionExecution.ExecuteInstance(interactionId, input),
      hostname / "api" / "v3" / "interaction" / "apply",
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
