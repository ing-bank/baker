package examples.kotlin.interactions

import com.ing.baker.recipe.javadsl.Interaction
import examples.kotlin.ingredients.Address

interface CancelOrder : Interaction {
    object Success

    fun apply(orderId: String, unavailableProductIds: List<String>): Success
}
