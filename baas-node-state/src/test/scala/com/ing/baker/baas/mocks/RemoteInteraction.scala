package com.ing.baker.baas.mocks

import akka.actor.ActorSystem
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.baas.recipe.Events.ItemsReserved
import com.ing.baker.baas.recipe.Ingredients.{Item, ReservedItems}
import com.ing.baker.baas.mocks.Utils._
import com.ing.baker.recipe.scaladsl.Interaction
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.serialization.Encryption
import org.mockserver.integration.ClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.verify.VerificationTimes

import scala.concurrent.Future

class RemoteInteraction(mock: ClientAndServer, interaction: Interaction)(implicit system: ActorSystem, encryption: Encryption) {

  import system.dispatcher

  def publishesItsInterface: Future[Unit] = Future {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/v3/interface")
        .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(serialize(ProtocolInteractionExecution.InstanceInterface(interaction.name, interaction.inputIngredients.map(_.ingredientType))))
    )
  }

  def processesSuccessfullyAndFires(event: EventInstance): Future[Unit] = Future {
    mock.when(applyMatch).respond(
      response()
        .withStatusCode(200)
        .withBody(serialize(ProtocolInteractionExecution.InstanceExecutedSuccessfully(Some(event))))
    )
  }

  def receivedEvent(event: EventInstance): Future[Unit] = Future {
    mock.verify(applyMatch, VerificationTimes.exactly(1))
  }

  private def applyMatch =
    request()
      .withMethod("POST")
      .withPath("/api/v3/apply")
      .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")

}

