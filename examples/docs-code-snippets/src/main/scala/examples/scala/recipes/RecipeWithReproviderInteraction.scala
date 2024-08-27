package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import examples.scala.events.OrderPlaced
import examples.scala.interactions.ShipOrder

object RecipeWithReproviderInteraction {
  val recipe: Recipe = Recipe("Reprovider recipe")
    .withSensoryEvent(Event[OrderPlaced])
    .withInteraction(
      ShipOrder.interaction
        .isReprovider(true)
        .withRequiredEvent(Event[OrderPlaced])
    )
}