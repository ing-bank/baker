package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import examples.scala.events.{FraudCheckCompleted, OrderPlaced, PaymentReceived}

object RecipeWithSensoryEvents {
  val recipe: Recipe = Recipe(name = "example")
    .withSensoryEvents(
      Event[OrderPlaced],
      PaymentReceived.event,
      FraudCheckCompleted.event
    )
}