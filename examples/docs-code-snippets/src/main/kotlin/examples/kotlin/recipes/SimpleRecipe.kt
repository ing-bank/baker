package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.events.OrderPlaced
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object SimpleRecipe {
    val recipe = recipe("example recipe") {
        sensoryEvents {
            event<OrderPlaced>()
        }
        interaction<ShipOrder>() 
    }
}