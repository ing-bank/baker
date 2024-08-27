package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.OrderPlaced
import examples.kotlin.interactions.CancelOrder
import examples.kotlin.interactions.CheckStock
import examples.kotlin.interactions.CheckStock.*
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object WebShopRecipe {
    val recipe = recipe("web-shop recipe") {
        sensoryEvents {
            event<OrderPlaced>()
        }
        interaction<CheckStock>()
        interaction<ShipOrder> {
            requiredEvents {
                event<SufficientStock>()
            }
        }
        interaction<CancelOrder> {
            requiredEvents {
                event<OrderHasUnavailableItems>()
            }
        }
    }
}