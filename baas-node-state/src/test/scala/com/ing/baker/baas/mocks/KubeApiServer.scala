package com.ing.baker.baas.mocks

import cats.effect.IO
import cats.syntax.apply._
import com.ing.baker.baas.kubeapi
import com.ing.baker.baas.kubeapi.{Service, Services}
import com.ing.baker.baas.recipe.ItemReservationRecipe
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.Times
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.MediaType

class KubeApiServer(mock: ClientAndServer) {

  def registersRemoteComponents: IO[Unit] =
    respondWithEvents(interactionAndEventListenersServices) *> respondWithEmpty

  private def respondWithEvents(templates: Services): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/v1/namespaces/default/services")
        .withQueryStringParameter("watch", "true"),
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(templates.mock.mkString("\n"), MediaType.APPLICATION_JSON)
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
        .withBody("{}", MediaType.APPLICATION_JSON)
    )
  }

  private def mockPort: kubeapi.PodPort =
    kubeapi.PodPort(
      name = "http-api",
      port = mock.getLocalPort,
      targetPort = Left(mock.getLocalPort))

  private def interactionServices: kubeapi.Services =
    kubeapi.Services(List(
      kubeapi.Service(
        metadata_name = "localhost",
        metadata_labels = Map("baas-component" -> "remote-interaction"),
        spec_ports = List(mockPort))
    )
    )

  private def interactionAndEventListenersServices: kubeapi.Services =
    interactionServices.++(kubeapi.Service(
      metadata_name = "localhost",
      metadata_labels = Map(
        "baas-component" -> "remote-event-listener",
        "baker-recipe" -> ItemReservationRecipe.compiledRecipe.name
      ),
      spec_ports = List(mockPort)
    ))
}
