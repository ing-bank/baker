package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import examples.scala.events.OrderPlaced
import examples.scala.interactions.{CancelOrder, CheckStock, ShipOrder}

object WebShopRecipe {
  val recipe: Recipe = Recipe("web-shop recipe")
    .withSensoryEvent(
      Event[OrderPlaced]
    )
    .withInteractions(
      CheckStock.interaction,
      ShipOrder.interaction
        .withRequiredEvent(
          Event[CheckStock.SufficientStock]
        ),
      CancelOrder.interaction
        .withRequiredEvent(
          Event[CheckStock.OrderHasUnavailableItems]
        )
    )
}