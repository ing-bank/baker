package com.ing.baker.baas.mocks

import akka.actor.ActorSystem
import com.ing.baker.runtime.serialization.Encryption
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.verify.VerificationTimes

import scala.concurrent.Future

class RemoteEventListener(mock: ClientAndServer)(implicit system: ActorSystem, encryption: Encryption) {

  import system.dispatcher

  private val eventApply: HttpRequest =
    request()
      .withMethod("POST")
      .withPath("/api/v3/recipe-event")
      .withHeader("X-Bakery-Intent", s"Remote-Event-Listener:localhost")

  def listensToEvents: Future[Unit] = Future {
    mock.when(eventApply).respond(
      response()
        .withStatusCode(200)
    )
  }

  def verifyEventsReceived(times: Int): Future[Unit] = Future {
    mock.verify(eventApply, VerificationTimes.exactly(times))
  }

  def verifyNoEventsArrived: Future[Unit] = Future {
    mock.verify(eventApply, VerificationTimes.exactly(0))
  }
}

