package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.FraudCheckCompleted
import examples.kotlin.events.OrderPlaced
import examples.kotlin.events.PaymentReceived

@ExperimentalDsl
object RecipeWithSensoryEvents {
    val recipe = recipe(name = "example") {
        sensoryEvents {
            eventWithoutFiringLimit<OrderPlaced>()
            event<PaymentReceived>()
            event<FraudCheckCompleted>(maxFiringLimit = 5)
        }
    }
}