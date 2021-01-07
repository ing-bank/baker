package com.ing.bakery.interaction

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.bakery.protocol.InteractionExecution
import io.prometheus.client.CollectorRegistry
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.client.middleware.Metrics
import org.http4s.dsl.io._
import org.http4s.metrics.prometheus.Prometheus
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

  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  implicit val interactionEntityDecoder: EntityDecoder[IO, List[InteractionExecution.Interaction]] = jsonOf[IO,  List[InteractionExecution.Interaction]]
  implicit val interactionsWithVersionEntityDecoder: EntityDecoder[IO, InteractionExecution.InteractionsWithVersion] = jsonOf[IO,  InteractionExecution.InteractionsWithVersion]
  implicit val executeRequestEntityEncoder: EntityEncoder[IO, List[IngredientInstance]] = jsonEncoderOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityDecoder: EntityDecoder[IO, InteractionExecution.ExecutionResult] = jsonOf[IO, InteractionExecution.ExecutionResult]

  def interface: IO[List[InteractionExecution.Interaction]] =
    client.expect[List[InteractionExecution.Interaction]]( GET(
      hostname / "api" / "bakery" / "interactions"
    ))

  def interfaceWithVersion: IO[InteractionExecution.InteractionsWithVersion] = {
    for {
      request <- GET(hostname / "api" / "bakery" / "interactions-with-version")
      status <- client.status(request)
      response <- {
        // Backwards compatibility for Bakery 3.1 interaction nodes that DO NOT publish the "interactions-with-version" endpoint
        if (status.code == 404) interface.map(InteractionExecution.InteractionsWithVersion("skip-check", _))
        else client.expect[InteractionExecution.InteractionsWithVersion](request)
      }
    } yield response
  }

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
