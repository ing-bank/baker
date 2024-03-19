package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.OrderPlaced
import examples.kotlin.events.PaymentReceived
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object RecipeWithReproviderInteraction {
    val recipe = recipe("Reprovider recipe") {
        sensoryEvents {
            event<OrderPlaced>()
        }
        interaction<ShipOrder> {
            isReprovider = true
            requiredEvents { event<OrderPlaced>() }
        }
    }
}