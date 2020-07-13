package com.ing.baker.baas.mocks

import cats.effect.IO
import com.ing.baker.baas.protocol.{InteractionExecution=>I}
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance}
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.Times
import org.mockserver.model.HttpRequest
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.verify.VerificationTimes
import io.circe.syntax._

class RemoteInteraction(mock: ClientAndServer, interaction: InteractionInstance) {
  import com.ing.baker.baas.protocol.InteractionExecutionJsonCodecs._

  def processesSuccessfullyAndFires(event: EventInstance): IO[Unit] = IO {
    mock.when(
      applyMatch,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(I.ExecutionResult(Right(I.Success(Some(event)))).asJson.toString),
    )
  }

  def processesWithFailure(e: Throwable): IO[Unit] = IO {
    mock.when(
      applyMatch,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(I.ExecutionResult(Left(I.Failure(I.InteractionError(e.getMessage)))).asJson.toString)
    )
  }

  def didNothing: IO[Unit] = IO {
    mock.verify(applyMatch, VerificationTimes.exactly(0))
  }

  def receivedEvent(event: EventInstance): IO[Unit] = IO {
    mock.verify(applyMatch, VerificationTimes.exactly(1))
  }

  private def applyMatch: HttpRequest =
    request()
      .withMethod("POST")
//      .withPath(s"/api/bakery/interaction/apply")
      .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")

}

