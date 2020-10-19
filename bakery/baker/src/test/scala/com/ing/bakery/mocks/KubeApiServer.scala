package com.ing.bakery.mocks

import java.util.concurrent.TimeUnit

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.protocol.{InteractionExecution => I}
import com.ing.bakery.mocks.WatchEvent.WatchEventType
import io.circe.syntax._
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.{TimeToLive, Times}
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.{HttpRequest, MediaType}
import play.api.libs.json.Format
import skuber.{ConfigMap, ObjectMeta}

class KubeApiServer(mock: ClientAndServer, interaction: InteractionInstance) {

  def deployInteraction(scope: String = "webshop"): IO[Unit] =
    respondWithEvents(scope, eventOfInteractionManifest(mock.getLocalPort, WatchEvent.Added, scope)) *> noNewInteractions(scope)

  def deleteInteraction(scope: String = "webshop"): IO[Unit] =
    respondWithEvents(scope, eventOfInteractionManifest(mock.getLocalPort, WatchEvent.Deleted, scope)) *> noNewInteractions(scope)

  def noNewInteractions(scope: String = "webshop"): IO[Unit] = IO {
    mock.when(watchMatch(scope)).respond(
      response()
        .withStatusCode(200)
        .withBody("", MediaType.APPLICATION_JSON)
        .withDelay(TimeUnit.MILLISECONDS, 100)
    )
  }

  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  private def eventOfInteractionManifest(port: Int, tpe: WatchEventType, scope: String): WatchEvent = {
    val creationContractName: String = "test-interaction-manifest"
    val interfaces = List(I.Interaction(interaction.shaBase64, interaction.name, interaction.input.toList))
    new WatchEvent {
      override type Resource = skuber.ConfigMap
      override def item: Resource = {
        val name = creationContractName
        val interactionsData = interfaces.asJson.toString
        ConfigMap(
          metadata = ObjectMeta(name = name, labels = Map("bakery-manifest" -> "interactions", "scope" -> scope)),
          data = Map("address" -> s"http://localhost:$port/", "interfaces" -> interactionsData)
        )
      }
      override def fmt: Format[Resource] = skuber.json.format.configMapFmt
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
      .withPath("/api/v1/namespaces/default/configmaps")
      .withQueryStringParameter("watch", "true")
      .withQueryStringParameter("labelSelector", "bakery-manifest=interactions,scope in (" + scope + ")",
      )
}
