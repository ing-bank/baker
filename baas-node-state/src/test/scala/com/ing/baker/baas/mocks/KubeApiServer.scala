package com.ing.baker.baas.mocks

import java.util.concurrent.TimeUnit

import cats.effect.IO
import cats.syntax.apply._
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.{TimeToLive, Times}
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.MediaType

class KubeApiServer(mock: ClientAndServer) {

  def deployInteractionService: IO[Unit] =
    respondWithEvents(WatchEvent.ofInteractionService(mock.getLocalPort, WatchEvent.Added)) *> respondWithEmpty

  def deleteInteractionService: IO[Unit] =
    respondWithEvents(WatchEvent.ofInteractionService(mock.getLocalPort, WatchEvent.Deleted)) *> respondWithEmpty

  private def respondWithEvents(events: WatchEvent*): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/v1/namespaces/default/services")
        .withQueryStringParameter("watch", "true"),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(events.mkString(","), MediaType.APPLICATION_JSON)
    )
  }

  private def respondWithEmpty: IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/v1/namespaces/default/services")
        .withQueryStringParameter("watch", "true")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody("", MediaType.APPLICATION_JSON)
        .withDelay(TimeUnit.SECONDS, 2)
    )
  }
}
