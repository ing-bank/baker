package com.ing.bakery.interaction

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceDescriptor}
import com.ing.baker.runtime.serialization.InteractionExecution
import io.circe.{Decoder, Encoder}
import io.circe.generic.semiauto.{deriveDecoder, deriveEncoder}
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.dsl.io._
import org.http4s.{Uri, _}

import scala.concurrent.ExecutionContext

object RemoteInteractionClient {


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

  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
  import com.ing.baker.runtime.serialization.JsonCodec._

  implicit val interactionEntityDecoder: EntityDecoder[IO, List[InteractionExecution.Descriptor]] = jsonOf[IO, List[InteractionExecution.Descriptor]]

  implicit val executeRequestEntityEncoder: EntityEncoder[IO, List[IngredientInstance]] = jsonEncoderOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityDecoder: EntityDecoder[IO, InteractionExecution.ExecutionResult] = jsonOf[IO, InteractionExecution.ExecutionResult]

  def interface: IO[List[InteractionExecution.Descriptor]] =
    client.expect[List[InteractionExecution.Descriptor]]( GET(
      hostname / "api" / "bakery" / "interactions"
    ))

  def runInteraction(interactionId: String, input: Seq[IngredientInstance]): IO[Option[EventInstance]] = {
    val request = POST(
      input.toList,
      hostname / "api" / "bakery" / "interactions" / interactionId / "execute")
    client.expect[InteractionExecution.ExecutionResult](request)
      .flatMap {
        case InteractionExecution.ExecutionResult(Right(success)) =>
          IO.pure(success.result)
        case InteractionExecution.ExecutionResult(Left(error)) =>
          IO.raiseError(new RuntimeException(s"Remote interaction execution failed; reason: ${error.reason}"))
      }
  }
}
