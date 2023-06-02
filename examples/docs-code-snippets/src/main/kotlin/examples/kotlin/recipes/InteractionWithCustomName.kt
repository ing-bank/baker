package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import examples.kotlin.interactions.ShipOrder

@ExperimentalDsl
object InteractionWithCustomName {
    val recipe = recipe("example") {
        interaction<ShipOrder> {
            name = "ship-order"
        }
    }
}