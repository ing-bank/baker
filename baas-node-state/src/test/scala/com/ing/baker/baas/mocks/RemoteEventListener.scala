package com.ing.baker.baas.mocks

import cats.effect.IO
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.verify.VerificationTimes

class RemoteEventListener(mock: ClientAndServer) {

  private val eventApply: HttpRequest =
    request()
      .withMethod("POST")
      .withPath("/api/v3/recipe-event")
      .withHeader("X-Bakery-Intent", s"Remote-Event-Listener:localhost")

  def listensToEvents: IO[Unit] = IO {
    mock.when(eventApply).respond(
      response()
        .withStatusCode(200)
    )
  }

  def verifyEventsReceived(times: Int): IO[Unit] = IO {
    mock.verify(eventApply, VerificationTimes.exactly(times))
  }

  def verifyNoEventsArrived: IO[Unit] = IO {
    mock.verify(eventApply, VerificationTimes.exactly(0))
  }
}

