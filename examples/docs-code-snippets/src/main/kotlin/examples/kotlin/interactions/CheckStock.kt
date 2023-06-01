package examples.kotlin.interactions

import com.ing.baker.recipe.javadsl.Interaction

interface CheckStock : Interaction {

    sealed interface Outcome

    data class OrderHasUnavailableItems(
        val unavailableProductIds: List<String>
    ) : Outcome

    object SufficientStock : Outcome

    fun apply(orderId: String, productIds: List<String>): Outcome
}
