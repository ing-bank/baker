package com.ing.baker.baas.interaction

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.interaction.BakeryHttp.Headers.{Intent, `X-Bakery-Intent`}
import com.ing.baker.baas.protocol.{InteractionExecution => I}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import io.circe.generic.auto._
import org.http4s.{Uri, _}
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.dsl.io._

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

  import com.ing.baker.baas.protocol.InteractionExecutionJsonCodecs._

  implicit val interactionEntityDecoder: EntityDecoder[IO, List[I.Interaction]] = jsonOf[IO,  List[I.Interaction]]
  implicit val executeRequestEntityEncoder: EntityEncoder[IO, List[IngredientInstance]] = jsonEncoderOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityDecoder: EntityDecoder[IO, Either[I.Success, I.Failure]] = jsonOf[IO, Either[I.Success, I.Failure]]

  def interface: IO[List[I.Interaction]] =
    client.expect[List[I.Interaction]]( GET(
      hostname / "api" / "bakery" / "interactions",
      `X-Bakery-Intent`(Intent.`Remote-Interaction`, hostname)
    ))

  def runInteraction(interactionId: String, input: List[IngredientInstance]): IO[Option[EventInstance]] = {
    val request = POST(
      input,
      hostname / "api" / "bakery" / "interactions" / interactionId / "execute",
      `X-Bakery-Intent`(Intent.`Remote-Interaction`, hostname)
    )
    client.expect[Either[
      I.Success,
      I.Failure]](request)
      .flatMap {
      case Left(result) =>
        IO.pure(result.result)
      case Right(e) =>
        IO.raiseError(new RuntimeException(s"Remote interaction execution failed; reason: ${e.reason}"))
    }
  }
}
