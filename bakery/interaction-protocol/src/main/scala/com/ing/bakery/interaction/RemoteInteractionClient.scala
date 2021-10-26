package com.ing.bakery.interaction

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.common.RemoteInteractionExecutionException
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.runtime.serialization.InteractionExecution
import com.ing.baker.runtime.serialization.InteractionExecution._
import com.ing.bakery.metrics.MetricService
import io.prometheus.client.Counter
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.blaze.client.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.dsl.io._
import org.http4s._

import scala.concurrent.ExecutionContext

object RemoteInteractionClient {

  lazy val InteractionSuccessCounter: Counter = MetricService.counter("bakery_interaction_success", "Successful interaction calls")
  lazy val InteractionFailureCounter: Counter = MetricService.counter("bakery_interaction_failure", "Failed interaction calls")

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(uri: Uri, pool: ExecutionContext, tlsConfig: Option[BakeryHttp.TLSConfig])(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, RemoteInteractionClient] =
    BlazeClientBuilder[IO](pool, tlsConfig.map(BakeryHttp.loadSSLContext))
      .withCheckEndpointAuthentication(false)
      .resource
      .map(new RemoteInteractionClient(_, uri))
}

final class RemoteInteractionClient(client: Client[IO], uri: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {
  import RemoteInteractionClient._
  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
  import com.ing.baker.runtime.serialization.JsonCodec._

  implicit val interactionEntityDecoder: EntityDecoder[IO, List[Descriptor]] = jsonOf[IO, List[Descriptor]]

  implicit val executeRequestEntityEncoder: EntityEncoder[IO, List[IngredientInstance]] = jsonEncoderOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityDecoder: EntityDecoder[IO, ExecutionResult] = jsonOf[IO, ExecutionResult]

  def interface: IO[List[InteractionExecution.Descriptor]] =
    client.expect[List[InteractionExecution.Descriptor]](GET(uri))

  def runInteraction(interactionId: String, input: Seq[IngredientInstance]): IO[Option[EventInstance]] = {
    val request = POST(
      input.toList,
      uri / interactionId / "execute")
    client.expect[ExecutionResult](request)
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
