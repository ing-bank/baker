package com.ing.baker.runtime.inmemory.recipe

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.Recipe
import com.ing.baker.recipe.kotlindsl.recipe
import com.ing.baker.runtime.inmemory.recipe.SendInvoice.InvoiceSent
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.CustomerInfoReceived
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.OrderPlaced
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.PaymentMade
import com.ing.baker.runtime.inmemory.recipe.ShipGoods.GoodsShipped
import com.ing.baker.runtime.inmemory.recipe.ValidateOrder.OrderValid
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

data class CustomerInfo(
    val name: String,
    val address: String,
    val email: String,
)

class SensoryEvents {
    class PaymentMade
    data class OrderPlaced(val order: String)
    data class CustomerInfoReceived(val customerInfo: CustomerInfo)
    data class CheckLimitGuard(val limitGuardKey: String)
}

object WebShopRecipe {
    @ExperimentalDsl
    @JvmStatic
    val recipe: Recipe = recipe("webshop") {
        sensoryEvents {
            event<OrderPlaced>()
            event<CustomerInfoReceived>()
            event<PaymentMade>()
        }
        interaction<ManufactureGoods> {
            requiredEvents {
                event<PaymentMade>()
                event<OrderValid>()
            }
        }
        interaction<ValidateOrder>()
        interaction<SendInvoice> {
            requiredEvents {
                event<GoodsShipped>()
            }
            // This is the  failure strategy specific for the SendInvoice interaction
            // If this Interaction fails with a technical exception the SendInvoiceExhaustedEvent is fired,
            // After this event the interaction is blocked from new executions
            failureStrategy = fireEventAndBlock("SendInvoiceExhaustedEvent")
        }
        interaction<ShipGoods> {
            // This is the failure strategy specific for the ShipGoods interaction
            // Once a Technical error occurs it will retry starting after 100 milliseconds
            // It will do it for 20 minutes with incremental increase up to 10 seconds between retries.
            // After it has retried for 20 minutes without a success the ShipGoodsExhaustedEvent will be fired.
            failureStrategy = retryWithIncrementalBackoff {
                until = deadline(1.seconds)
                initialDelay = 10.milliseconds
                maxTimeBetweenRetries = 100.milliseconds
                fireEventAndBlock = "ShipGoodsExhaustedEvent"
            }
        }
        checkpointEvent("RecipeSuccessful") {
            requiredEvents {
                event<GoodsShipped>()
                event<InvoiceSent>()
            }
        }
        interaction<LogRecipeFailed> {
            requiredOneOfEvents {
                event("ShipGoodsExhaustedEvent")
                event("SendInvoiceExhaustedEvent")
            }
        }
        // This is the default failure strategy for the Recipe.
        // For any interaction that does not have a failure strategy configured this will be taken.
        // Important note: the withFireEvent is not supported on the DefaultFailureStrategy.
        defaultFailureStrategy = retryWithIncrementalBackoff {
            until = deadline(1.seconds)
            initialDelay = 10.milliseconds
            maxTimeBetweenRetries = 100.milliseconds
        }
        //For Bakery users it is mandatory to set a RetentionPeriod to comply to GDPR.
        //This is how long an instance of this process is kept in the data store on the Bakery side.
        retentionPeriod = 14.days
    }
}
