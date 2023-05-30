package examples.kotlin.interactions

import com.ing.baker.recipe.javadsl.Interaction

interface ShipItems : Interaction {
    object Success

    fun apply(orderId: String): Success
}
