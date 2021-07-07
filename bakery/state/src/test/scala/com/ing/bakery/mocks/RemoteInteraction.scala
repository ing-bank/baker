package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceInput}
import com.ing.baker.runtime.serialization.{InteractionExecution => I}
import com.ing.bakery.recipe.Interactions
import io.circe.syntax._
import org.mockserver.integration.ClientAndServer
import org.mockserver.matchers.Times
import org.mockserver.model.HttpRequest
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.verify.VerificationTimes

class RemoteInteraction(mock: ClientAndServer) {
  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._

  def respondsWithInterfaces(): IO[Unit] = IO {
    mock.when(
      receivedInquiry,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
            .withBody(List(I.Descriptor("localhost", Interactions.ReserveItemsInteraction.name,
              Interactions.ReserveItemsInteraction.inputIngredients.map(i => InteractionInstanceInput(Some(i.name), i.ingredientType)).toList,
              Some(Interactions.ReserveItemsInteraction.output.map(e => e.name -> e.providedIngredients.map(i => i.name -> i.ingredientType).toMap).toMap))
            ).asJson.toString)
    )
  }

  def processesSuccessfullyAndFires(event: EventInstance): IO[Unit] = IO {
    mock.when(
      receivedExecutionRequest,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(I.ExecutionResult(Right(I.Success(Some(event)))).asJson.toString),
    )
  }

  def processesWithFailure(e: Throwable): IO[Unit] = IO {
    mock.when(
      receivedExecutionRequest,
      Times.exactly(1)
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(I.ExecutionResult(Left(I.Failure(I.InteractionError("interaction",
          e.getMessage)))).asJson.toString)
    )
  }

  def didNothing: IO[Unit] = IO {
    mock.verify(receivedExecutionRequest, VerificationTimes.exactly(0))
  }

  def receivedEvent(event: EventInstance): IO[Unit] = IO {
    mock.verify(receivedExecutionRequest, VerificationTimes.exactly(1))
  }

  private def receivedExecutionRequest: HttpRequest =
    request()
      .withMethod("POST")

  private def receivedInquiry: HttpRequest =
    request()
      .withPath("/api/bakery/interactions")
      .withMethod("GET")

}

