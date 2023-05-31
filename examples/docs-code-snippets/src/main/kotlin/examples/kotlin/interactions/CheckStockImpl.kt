package examples.kotlin.interactions

object CheckStockImpl : CheckStock {
    override fun apply(orderId: String, productIds: List<String>): CheckStock.Outcome {
        println("Checking stock for order: $orderId and products: $productIds")

        // Flip a coin to determine if we have enough stock.
        return if ((1..1000).random() < 500) {
            CheckStock.Success
        } else {
            CheckStock.OrderHasUnavailableItems(productIds)
        }
    }
}