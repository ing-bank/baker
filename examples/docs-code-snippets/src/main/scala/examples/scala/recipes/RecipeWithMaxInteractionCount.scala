package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.interactions.ShipOrder

object RecipeWithMaxInteractionCount {
  val recipe: Recipe = Recipe("example")
    .withInteraction(
      ShipOrder.interaction
        .withMaximumInteractionCount(1)
    )
}