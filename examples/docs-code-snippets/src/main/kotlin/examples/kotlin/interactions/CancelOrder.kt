package examples.kotlin.interactions

import com.ing.baker.recipe.javadsl.Interaction

interface CancelOrder : Interaction {
    object OrderCancelled

    fun apply(orderId: String, unavailableProductIds: List<String>): OrderCancelled
}
