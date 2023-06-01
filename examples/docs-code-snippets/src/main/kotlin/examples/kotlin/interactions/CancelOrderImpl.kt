package examples.kotlin.interactions

object CancelOrderImpl : CancelOrder {
    override fun apply(orderId: String, unavailableProductIds: List<String>): CancelOrder.OrderCancelled {
        println("Canceling order $orderId. The following products are unavailable: $unavailableProductIds")
        return CancelOrder.OrderCancelled
    }
}