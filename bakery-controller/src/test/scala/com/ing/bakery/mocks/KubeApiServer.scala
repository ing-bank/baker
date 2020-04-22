package com.ing.bakery.mocks

import java.util.concurrent.TimeUnit

import cats.effect.IO
import com.ing.bakery.clustercontroller.controllers.{BakerResource, InteractionResource}
import com.ing.bakery.mocks.WatchEvent.{ResourcePath, WatchEventType}
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.{TimeToLive, Times}
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.{HttpRequest, MediaType}
import org.mockserver.verify.VerificationTimes

class KubeApiServer(mock: ClientAndServer) {

  def createBakers(resource: BakerResource*): IO[Unit] =
    eventsFor(watchResourceMatch(ResourcePath.BakersPath), resource.map(WatchEvent.of(_, WatchEventType.Added)): _*)

  def deleteBakers(resource: BakerResource*): IO[Unit] =
    eventsFor(watchResourceMatch(ResourcePath.BakersPath), resource.map(WatchEvent.of(_, WatchEventType.Deleted)): _*)

  def updateBakers(resource: BakerResource*): IO[Unit] =
    eventsFor(watchResourceMatch(ResourcePath.BakersPath), resource.map(WatchEvent.of(_, WatchEventType.Modified)): _*)

  def noNewBakerEvents: IO[Unit] =
    emptyEventsFor(watchResourceMatch(ResourcePath.BakersPath))

  def createInteractions(resource: InteractionResource*): IO[Unit] =
    eventsFor(watchResourceMatch(ResourcePath.InteractionsPath), resource.map(WatchEvent.of(_, WatchEventType.Added)): _*)

  def deleteInteractions(resource: InteractionResource*): IO[Unit] =
    eventsFor(watchResourceMatch(ResourcePath.InteractionsPath), resource.map(WatchEvent.of(_, WatchEventType.Deleted)): _*)

  def updateInteractions(resource: InteractionResource*): IO[Unit] =
    eventsFor(watchResourceMatch(ResourcePath.InteractionsPath), resource.map(WatchEvent.of(_, WatchEventType.Modified)): _*)

  def noNewInteractionEvents: IO[Unit] =
    emptyEventsFor(watchResourceMatch(ResourcePath.InteractionsPath))

  private def watchResourceMatch(resourcePath: ResourcePath): HttpRequest =
    request()
      .withMethod("GET")
      .withPath(resourcePath.toString)

  private def emptyEventsFor(httpMatch: HttpRequest): IO[Unit] = IO {
    mock.when(httpMatch
      .withQueryStringParameter("watch", "true")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody("", MediaType.APPLICATION_JSON)
        .withDelay(TimeUnit.MILLISECONDS, 1000)
    )
  }

  private def eventsFor(httpMatch: HttpRequest, events: WatchEvent*): IO[Unit] = IO {
    mock.when(
      httpMatch
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

  def expectCreationOf(jsonPath: String, resourcePath: ResourcePath): IO[Unit] = IO {
    val json = scala.io.Source.fromResource(jsonPath).mkString
    mock.when(
      request().withMethod("POST").withPath(resourcePath.toString),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(201)
        .withBody(json, MediaType.APPLICATION_JSON)
    )
  }

  def validateCreationOf(jsonPath: String, resourcePath: ResourcePath): IO[Unit] = IO {
    mock.verify(request().withMethod("POST").withPath(resourcePath.toString), VerificationTimes.exactly(1))
  }
}
