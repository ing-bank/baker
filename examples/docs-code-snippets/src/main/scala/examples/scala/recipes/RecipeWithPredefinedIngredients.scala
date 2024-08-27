package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.interactions.ShipOrder

object RecipeWithPredefinedIngredients {
  val recipe: Recipe = Recipe("example")
    .withInteraction(
      ShipOrder.interaction
        .withPredefinedIngredients(
          ("shippingCostAmount", BigDecimal("5.75")),
          ("shippingCostCurrency", "EUR")
        )
    )
}