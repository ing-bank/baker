package com.ing.baker.baas.mocks

import java.util.concurrent.TimeUnit

import cats.effect.IO
import cats.syntax.apply._
import io.circe.syntax._
import com.ing.baker.baas.mocks.WatchEvent.WatchEventType
import com.ing.baker.baas.protocol.{InteractionExecution => I}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.{TimeToLive, Times}
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.{HttpRequest, MediaType}
import play.api.libs.json.Format
import skuber.{ConfigMap, ObjectMeta}

class KubeApiServer(mock: ClientAndServer, interaction: InteractionInstance) {

  def deployInteraction: IO[Unit] =
    respondWithEvents(eventOfInteractionCreationContract(mock.getLocalPort, WatchEvent.Added)) *> noNewInteractions

  def deleteInteraction: IO[Unit] =
    respondWithEvents(eventOfInteractionCreationContract(mock.getLocalPort, WatchEvent.Deleted)) *> noNewInteractions

  def noNewInteractions: IO[Unit] = IO {
    mock.when(watchMatch).respond(
      response()
        .withStatusCode(200)
        .withBody("", MediaType.APPLICATION_JSON)
        .withDelay(TimeUnit.MILLISECONDS, 100)
    )
  }

  private val baasComponentLabel: (String, String) = "baas-component" -> "remote-interaction-interfaces"
  import com.ing.baker.baas.protocol.InteractionExecutionJsonCodecs._

  private def eventOfInteractionCreationContract(port: Int, tpe: WatchEventType): WatchEvent = {
    val creationContractName: String = "interactions-test-interaction"
    val interfaces = List(I.Interaction(interaction.shaBase64, interaction.name, interaction.input))
    new WatchEvent {
      override type Resource = skuber.ConfigMap
      override def item: Resource = {
        val name = creationContractName
        val interactionsData = interfaces.asJson.toString
        ConfigMap(
          metadata = ObjectMeta(name = name, labels = Map(baasComponentLabel)),
          data = Map("address" -> s"http://localhost:$port/", "interfaces" -> interactionsData)
        )
      }
      override def fmt: Format[Resource] = skuber.json.format.configMapFmt
      override def eventType: WatchEventType = tpe
    }
  }

  private def respondWithEvents(events: WatchEvent*): IO[Unit] = IO {
    mock.when(
      watchMatch,
      Times.exactly(1),
      TimeToLive.unlimited(),
      10
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(events.mkString(","), MediaType.APPLICATION_JSON)
    )
  }

  private def watchMatch: HttpRequest =
    request()
      .withMethod("GET")
      .withPath("/api/v1/namespaces/default/configmaps")
      .withQueryStringParameter("watch", "true")
      .withQueryStringParameter("labelSelector", baasComponentLabel._1 + "=" + baasComponentLabel._2)
}
