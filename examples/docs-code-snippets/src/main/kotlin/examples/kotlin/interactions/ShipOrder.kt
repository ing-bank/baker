package examples.kotlin.interactions

import com.ing.baker.recipe.javadsl.Interaction
import examples.kotlin.ingredients.Address

interface ShipOrder : Interaction {
    object Success

    fun apply(orderId: String, address: Address): Success
}
