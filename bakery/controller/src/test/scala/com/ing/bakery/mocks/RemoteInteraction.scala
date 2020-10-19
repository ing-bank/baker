package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.protocol.{InteractionExecution => I}
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import io.circe.syntax._

class RemoteInteraction(mock: ClientAndServer) {
  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

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
          List(I.Interaction(interaction.shaBase64, interaction.name, interaction.input.toList)).asJson.toString
        )
    )
  }

  def publishesItsInterfaceWithVersion(version: String, interaction: InteractionInstance): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions-with-version")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(
          I.InteractionsWithVersion(
            version,
            List(I.Interaction(interaction.shaBase64, interaction.name, interaction.input.toList))
          ).asJson.toString
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

  def interfaceWithVersionWasQueried: IO[Unit] = IO {
    mock.verify(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions-with-version")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost"))
  }
}
