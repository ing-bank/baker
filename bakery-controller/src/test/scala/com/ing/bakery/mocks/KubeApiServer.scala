package com.ing.bakery.mocks

import cats.effect.IO
import cats.syntax.apply._
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.Times
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.MediaType
import play.api.libs.json.Format
import skuber.{ObjectResource, ResourceDefinition}

class KubeApiServer(mock: ClientAndServer) {

  def resourceWatchResponds[O <: ObjectResource](path: WatchEvent.ResourcePath, tpe: WatchEvent.WatchEventType, resources: O*)(implicit fmt: Format[O], rd: ResourceDefinition[O]): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath(path.toString)
        .withQueryStringParameter("watch", "true"),
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(resources.map(WatchEvent(_, tpe).toString).mkString("\n"), MediaType.APPLICATION_JSON)
    )
  } *> resourceWatchRespondsEmpty(path)

  def resourceWatchRespondsEmpty(path: WatchEvent.ResourcePath): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath(path.toString)
        .withQueryStringParameter("watch", "true")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody("{}", MediaType.APPLICATION_JSON)
    )
  }
}
