package examples.kotlin.events

data class OrderPlaced(
    val orderId: String,
    val productIds: List<String>
)