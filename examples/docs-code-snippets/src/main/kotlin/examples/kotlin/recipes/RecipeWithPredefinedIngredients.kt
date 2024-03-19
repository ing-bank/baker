package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object RecipeWithPredefinedIngredients {
    val recipe = recipe("example") {
        interaction<ShipOrder> {
           preDefinedIngredients {
               "shippingCostAmount" to "5.75".toBigDecimal()
               "shippingCostCurrency" to "EUR"
           }
        }
    }
}