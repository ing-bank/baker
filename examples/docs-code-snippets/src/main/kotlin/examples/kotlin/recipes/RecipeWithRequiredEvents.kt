package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.FraudCheckCompleted
import examples.kotlin.events.PaymentReceived
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object RecipeWithRequiredEvents {
    val recipe = recipe("example") {
        interaction<ShipOrder> {
            requiredEvents {
                event<FraudCheckCompleted>()
            }
            requiredOneOfEvents {
                event<PaymentReceived>()
                event(name = "UsedCouponCode")
            }
        }
    }
}