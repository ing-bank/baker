package com.ing.bakery.interaction

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.common.RemoteInteractionExecutionException
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.runtime.serialization.InteractionExecution
import com.ing.baker.runtime.serialization.InteractionExecution._
import com.ing.bakery.metrics.MetricService
import io.prometheus.client.Counter
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.dsl.io._
import org.http4s._

import scala.concurrent.ExecutionContext
import cats.effect.Temporal

object RemoteInteractionClient {

  lazy val InteractionSuccessCounter: Counter = MetricService.counter("bakery_interaction_success", "Successful interaction calls")
  lazy val InteractionFailureCounter: Counter = MetricService.counter("bakery_interaction_failure", "Failed interaction calls")

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(headers: Headers,
               pool: ExecutionContext,
               tlsConfig: Option[BakeryHttp.TLSConfig])(implicit timer: Temporal[IO]): Resource[IO, RemoteInteractionClient] =
    BlazeClientBuilder[IO](pool, tlsConfig.map(BakeryHttp.loadSSLContext))
      .withCheckEndpointAuthentication(false)
      .resource
      .map(new BaseRemoteInteractionClient(_, headers))
}

trait RemoteInteractionClient {
  def headers: Headers
  def entityCodecs: (EntityEncoder[IO, ExecutionRequest],  EntityDecoder[IO, ExecutionResult], EntityDecoder[IO, Interactions])
  def execute(uri: Uri, interactionId: String, input: Seq[IngredientInstance]): IO[Option[EventInstance]]
  def interfaces(uri: Uri): IO[Interactions]
}

class BaseRemoteInteractionClient(
                                            val client: Client[IO],
                                            val headers: Headers)(implicit cs: ContextShift[IO], timer: Temporal[IO])
  extends RemoteInteractionClient {
  import RemoteInteractionClient._
  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
  import com.ing.baker.runtime.serialization.JsonCodec._

  def entityCodecs:(EntityEncoder[IO, ExecutionRequest],  EntityDecoder[IO, ExecutionResult], EntityDecoder[IO, Interactions])  =
    (jsonEncoderOf[IO, ExecutionRequest],
      jsonOf[IO, ExecutionResult],
      jsonOf[IO, Interactions])

  private implicit lazy val (interactionEntityDecoder, executeRequestEntityEncoder, executeResponseEntityDecoder) = entityCodecs

  def interfaces(uri: Uri): IO[Interactions] =
    client.expect[Interactions](
      Request[IO](
        method = GET,
        uri = uri,
        headers = headers,
      )
    )

  def execute(uri: Uri, interactionId: String, input: Seq[IngredientInstance]): IO[Option[EventInstance]] = {
    client.expect[ExecutionResult](
      Request[IO](
        method = POST,
        uri = uri,
        headers = headers,
      ).withEntity(ExecutionRequest(interactionId, input.toList)))
      .flatMap {
        case InteractionExecution.ExecutionResult(Right(success)) =>
          IO {
            InteractionSuccessCounter.inc()
            success.result
          }
        case InteractionExecution.ExecutionResult(Left(error)) =>
          IO.raiseError {
            InteractionFailureCounter.inc()
            new RemoteInteractionExecutionException(error.reason.toString)
          }
      }
  }
}
