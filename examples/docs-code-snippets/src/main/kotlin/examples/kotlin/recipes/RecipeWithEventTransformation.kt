package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.OrderPlaced
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object RecipeWithEventTransformation {
    val recipe = recipe("example") {
        interaction<ShipOrder> {
           transformEvent<OrderPlaced>(newName = "OrderCreated") {
               "customerId" to "userId"
               "productIds" to "skus"
           }
        }
    }
}