package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
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
        .withPath("/api/v3/interaction")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(ProtoMap.ctxToProto(ProtocolInteractionExecution.Interfaces(List(
          ProtocolInteractionExecution.InstanceInterface(interaction.shaBase64, interaction.name, interaction.input)))).toByteArray)
    )
  }

  def interfaceWasQueried(interaction: InteractionInstance): IO[Unit] = IO {
    mock.verify(
      request()
        .withMethod("GET")
        .withPath("/api/v3/interaction")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost"))
  }
}
