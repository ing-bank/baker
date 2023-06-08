package examples.scala.recipes

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.interactions.ShipOrder

object RecipeWithFailureStrategy {
  val recipe: Recipe = Recipe("example")
    .withInteraction(
      ShipOrder.interaction
        .withFailureStrategy(
          InteractionFailureStrategy.FireEventAfterFailure(Some("shippingFailed"))
        )
    )
}