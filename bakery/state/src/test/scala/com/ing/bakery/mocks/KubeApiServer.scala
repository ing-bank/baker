package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.mocks.WatchEvent.WatchEventType
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.{TimeToLive, Times}
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.{HttpRequest, MediaType}
import play.api.libs.json.Format
import skuber.Service

import java.util.concurrent.TimeUnit

class KubeApiServer(mock: ClientAndServer) {

  def deployInteraction(scope: String = "webshop"): IO[Unit] =
    respondWithEvents(scope, eventOfInteractionService(mock.getLocalPort, WatchEvent.Added, scope)) *> noNewInteractions(scope)

  def deleteInteraction(scope: String = "webshop"): IO[Unit] =
    respondWithEvents(scope, eventOfInteractionService(mock.getLocalPort, WatchEvent.Deleted, scope)) *> noNewInteractions(scope)

  def noNewInteractions(scope: String = "webshop"): IO[Unit] = IO {
    mock.when(watchMatch(scope)).respond(
      response()
        .withStatusCode(200)
        .withBody("", MediaType.APPLICATION_JSON)
        .withDelay(TimeUnit.MILLISECONDS, 100)
    )
  }

  private def eventOfInteractionService(port: Int, tpe: WatchEventType, scope: String): WatchEvent = {
    new WatchEvent {
      override type Resource = skuber.Service
      override def item: skuber.Service =
        Service(
          name = "localhost",
          spec = Service.Spec(
            ports = List(Service.Port("interactions", skuber.Protocol.TCP, port, None, port)),
            selector = Map("scope" -> scope)
          )
        )

      override def fmt: Format[Resource] = skuber.json.format.serviceFmt
      override def eventType: WatchEventType = tpe
    }
  }

  private def respondWithEvents(scope: String, events: WatchEvent*): IO[Unit] = IO {
    mock.when(
      watchMatch(scope),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(events.mkString(","), MediaType.APPLICATION_JSON)
    )
  }

  private def watchMatch(scope: String): HttpRequest =
    request()
      .withMethod("GET")
      .withPath("/api/v1/namespaces/default/services")
      .withQueryStringParameter("watch", "true")
      .withQueryStringParameter("labelSelector", "scope=webshop")
}
