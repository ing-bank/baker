package examples.scala.recipes

import com.ing.baker.recipe.scaladsl
import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.events.{FraudCheckCompleted, PaymentReceived}

object RecipeWithCheckpointEvent {
  val recipe: Recipe = Recipe("example")
    .withCheckpointEvent(
      scaladsl.CheckPointEvent(
        name = "CheckpointReached",
        requiredEvents = Set.apply(
          PaymentReceived.event.name,
          FraudCheckCompleted.event.name
        )
      )
    )
}