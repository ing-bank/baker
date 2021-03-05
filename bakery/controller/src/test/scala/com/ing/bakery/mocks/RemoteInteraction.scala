package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.runtime.serialization.InteractionExecution
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import io.circe.syntax._
import org.mockserver.matchers.Times

class RemoteInteraction(mock: ClientAndServer) {
  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._

  def publishesItsInterface(interaction: InteractionInstance): IO[Unit] = IO {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(
          List(InteractionExecution.Descriptor(interaction.shaBase64, interaction.name, interaction.input.toList, interaction.output)).asJson.toString
        )
    )
  }

  def interfaceWasQueried: IO[Unit] = IO {
    mock.verify(
      request()
        .withMethod("GET")
        .withPath("/api/bakery/interactions")
    )
  }

}
