package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import examples.scala.events.OrderPlaced
import examples.scala.interactions.ShipOrder

object SimpleRecipe {
  val recipe: Recipe = Recipe("example recipe")
    .withSensoryEvent(Event[OrderPlaced])
    .withInteraction(ShipOrder.interaction)
}