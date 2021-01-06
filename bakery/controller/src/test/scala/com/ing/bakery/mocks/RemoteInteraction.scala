package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.protocol.{InteractionExecution => I}
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import io.circe.syntax._
import org.mockserver.matchers.Times

class RemoteInteraction(mock: ClientAndServer) {
  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  def publishesItsInterface(interaction: InteractionInstance): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions")
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

  def noInterfaceWithVersionAvailable: IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions-with-version"),
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(404)
    )
  }

  def interfaceWasQueried: IO[Unit] = IO {
    mock.verify(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions")
    )
  }

  def interfaceWithVersionWasQueried: IO[Unit] = IO {
    mock.verify(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions-with-version")
    )
  }
}
