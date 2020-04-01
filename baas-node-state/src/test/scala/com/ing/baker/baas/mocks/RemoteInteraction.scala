package com.ing.baker.baas.mocks

import cats.effect.IO
import com.ing.baker.baas.mocks.Utils._
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance}
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.Times
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.verify.VerificationTimes

class RemoteInteraction(mock: ClientAndServer, interaction: InteractionInstance) {

  def publishesItsInterface: IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/v3/interaction")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(serialize(ProtocolInteractionExecution.Interfaces(List(
          ProtocolInteractionExecution.InstanceInterface(interaction.shaBase64, interaction.name, interaction.input)))))
    )
  }

  def processesSuccessfullyAndFires(event: EventInstance): IO[Unit] = IO {
    mock.when(
      applyMatch,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(serialize(ProtocolInteractionExecution.InstanceExecutedSuccessfully(Some(event)))),
    )
  }

  def processesWithFailure(e: Throwable): IO[Unit] = IO {
    mock.when(
      applyMatch,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(serialize(ProtocolInteractionExecution.InstanceExecutionFailed(e.getMessage)))
    )
  }

  def didNothing: IO[Unit] = IO {
    mock.verify(applyMatch, VerificationTimes.exactly(0))
  }

  def receivedEvent(event: EventInstance): IO[Unit] = IO {
    mock.verify(applyMatch, VerificationTimes.exactly(1))
  }

  private def applyMatch =
    request()
      .withMethod("POST")
      .withPath(s"/api/v3/interaction/apply")
      .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")

}

