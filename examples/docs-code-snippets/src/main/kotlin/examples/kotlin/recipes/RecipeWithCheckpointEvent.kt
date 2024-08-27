package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.FraudCheckCompleted
import examples.kotlin.events.PaymentReceived

@ExperimentalDsl
object RecipeWithCheckpointEvent {
    val recipe = recipe("example") {
        checkpointEvent(eventName = "CheckpointReached") {
            requiredEvents {
                event<PaymentReceived>()
                event<FraudCheckCompleted>()
            }
        }
    }
}