package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.interactions.ShipOrder

object InteractionWithCustomName {
  val recipe: Recipe = Recipe("example")
    .withInteraction(
      ShipOrder.interaction
        .withName("ship-order")
    )
}