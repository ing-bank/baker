package examples.kotlin.events

import examples.kotlin.ingredients.Address

data class OrderPlaced(
    val orderId: String,
    val customerId: String,
    val address: Address,
    val productIds: List<String>
)