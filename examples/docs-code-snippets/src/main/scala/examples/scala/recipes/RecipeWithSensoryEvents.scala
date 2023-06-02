package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.events.{FraudCheckCompleted, OrderPlaced, PaymentReceived}

object RecipeWithSensoryEvents {
  val recipe: Recipe = Recipe(name = "example")
    .withSensoryEvents(
      OrderPlaced.event,
      PaymentReceived.event,
      FraudCheckCompleted.event
    )
}