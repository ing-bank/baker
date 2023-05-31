package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.events.OrderPlaced
import examples.scala.interactions.ShipOrder

object SimpleRecipe {
  val recipe: Recipe = Recipe("example recipe")
    .withSensoryEvent(OrderPlaced.event)
    .withInteraction(ShipOrder.interaction)
}