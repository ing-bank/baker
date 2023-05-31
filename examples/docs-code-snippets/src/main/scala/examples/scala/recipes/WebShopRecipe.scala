package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.events.OrderPlaced
import examples.scala.interactions.{CancelOrder, CheckStock, ShipOrder}

object WebShopRecipe {
  val recipe: Recipe = Recipe("web-shop recipe")
    .withSensoryEvent(OrderPlaced.event)
    .withInteractions(
      CheckStock.interaction,
      ShipOrder.interaction
        .withRequiredEvent(CheckStock.success),
      CancelOrder.interaction
        .withRequiredEvent(CheckStock.orderHasUnavailableItems)
    )
}