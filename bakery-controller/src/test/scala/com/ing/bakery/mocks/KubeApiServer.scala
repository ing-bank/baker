package com.ing.bakery.mocks

import java.util.concurrent.TimeUnit

import cats.effect.IO
import com.ing.bakery.clustercontroller.controllers.{BakerResource, InteractionResource}
import com.ing.bakery.mocks.WatchEvent.{ResourcePath, WatchEventType}
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.{TimeToLive, Times}
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.{HttpRequest, HttpResponse, MediaType}
import org.mockserver.verify.VerificationTimes
import skuber.ConfigMap
import skuber.json.format.configMapFmt

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

  def createConfigMapFor(component: String, resource: ConfigMap*): IO[Unit] =
    eventsFor(withLabelSelector(watchResourceMatch(ResourcePath.ConfigMapsPath), Some("custom-resource-definition" -> component)), resource.map(WatchEvent.of(_, WatchEventType.Added)): _*)

  def deleteConfigMapFor(component: String, resource: ConfigMap*): IO[Unit] =
    eventsFor(withLabelSelector(watchResourceMatch(ResourcePath.ConfigMapsPath), Some("custom-resource-definition" -> component)), resource.map(WatchEvent.of(_, WatchEventType.Deleted)): _*)

  def updateConfigMapFor(component: String, resource: ConfigMap*): IO[Unit] =
    eventsFor(withLabelSelector(watchResourceMatch(ResourcePath.ConfigMapsPath), Some("custom-resource-definition" -> component)), resource.map(WatchEvent.of(_, WatchEventType.Modified)): _*)

  def noNewInteractionEvents: IO[Unit] =
    emptyEventsFor(watchResourceMatch(ResourcePath.InteractionsPath))

  def noNewConfigMapEventsFor(component: String): IO[Unit] =
    emptyEventsFor(watchResourceMatch(ResourcePath.ConfigMapsPath, Some("custom-resource-definition" -> component)))

  private def watchResourceMatch(resourcePath: ResourcePath, labelSelector: Option[(String, String)] = None): HttpRequest =
    withLabelSelector(request()
      .withMethod("GET")
      .withPath(resourcePath.toString), labelSelector)

  private def emptyEventsFor(httpMatch: HttpRequest): IO[Unit] = IO {
    mock.when(httpMatch
      .withQueryStringParameter("watch", "true")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody("", MediaType.APPLICATION_JSON)
        .withDelay(TimeUnit.MILLISECONDS, 500)
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

  def expectGetOf(jsonPath: String, resourcePath: ResourcePath, transform: String => String = identity): IO[Unit] = IO {
    val json = transform(scala.io.Source.fromResource(jsonPath).mkString)
    mock.when(
      request().withMethod("GET").withPath(resourcePath.toString),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(json, MediaType.APPLICATION_JSON)
    )
  }

  def expectCreationOf(jsonPath: String, resourcePath: ResourcePath, transform: String => String = identity): IO[Unit] = IO {
    val json = transform(scala.io.Source.fromResource(jsonPath).mkString)
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

  def expectCreationOfAndReport409(resourcePath: ResourcePath): IO[Unit] = IO {
    val json = scala.io.Source.fromResource("expectations/status-409.json").mkString
    mock.when(
      request().withMethod("POST").withPath(resourcePath.toString),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(409)
        .withBody(json, MediaType.APPLICATION_JSON)
    )
  }

  def expectDeletionOf(resourcePath: ResourcePath, labelSelector: Option[(String, String)] = None, returnJsonPath: Option[String] = None): IO[Unit] = IO {
    mock.when(
      withLabelSelector(request().withMethod("DELETE").withPath(resourcePath.toString), labelSelector),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      withReturnJson(response()
        .withStatusCode(200), returnJsonPath)
    )
  }

  def expectUpdateOf(jsonPath: String, resourcePath: ResourcePath, transform: String => String = identity): IO[Unit] = IO {
    val json = transform(scala.io.Source.fromResource(jsonPath).mkString)
    mock.when(
      request().withMethod("PUT").withPath(resourcePath.toString),
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(201)
        .withBody(json, MediaType.APPLICATION_JSON)
    )
  }

  def validateCreationOf(resourcePath: ResourcePath): IO[Unit] = IO {
    mock.verify(request().withMethod("POST").withPath(resourcePath.toString), VerificationTimes.exactly(1))
  }

  def validateDeletionOf(resourcePath: ResourcePath, labelSelector: Option[(String, String)] = None): IO[Unit] = IO {
    mock.verify(withLabelSelector(request().withMethod("DELETE").withPath(resourcePath.toString), labelSelector), VerificationTimes.exactly(1))
  }

  def validateUpdateOf(resourcePath: ResourcePath): IO[Unit] = IO {
    mock.verify(request().withMethod("PUT").withPath(resourcePath.toString), VerificationTimes.exactly(1))
  }

  private def withLabelSelector(request: HttpRequest, labelSelector: Option[(String, String)]): HttpRequest =
    labelSelector.fold(request) { case (key, value) => request.withQueryStringParameter("labelSelector", s"$key=$value")}

  private def withReturnJson(response: HttpResponse, returnJsonPath: Option[String]): HttpResponse =
    returnJsonPath.fold(response) { path =>
      val json = scala.io.Source.fromResource(path).mkString
      response.withBody(json, MediaType.APPLICATION_JSON)
    }
}
