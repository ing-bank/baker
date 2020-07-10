package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.baas.protocol.InteractionExecution
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.runtime.serialization.ProtoMap
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response

class RemoteInteraction(mock: ClientAndServer) {

  def publishesItsInterface(interaction: InteractionInstance): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(
          List(
          InteractionExecution.Interaction(interaction.shaBase64, interaction.name, interaction.input))
        )
    )
  }

  def interfaceWasQueried(interaction: InteractionInstance): IO[Unit] = IO {
    mock.verify(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost"))
  }
}
