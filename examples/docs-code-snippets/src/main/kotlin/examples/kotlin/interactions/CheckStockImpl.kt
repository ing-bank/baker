package examples.kotlin.interactions

object CheckStockImpl : CheckStock {
    override fun apply(orderId: String, productIds: List<String>): CheckStock.Outcome {
        println("Checking stock for order: $orderId and products: $productIds")

        return if ((1..1000).random() < 500) {
            CheckStock.SufficientStock
        } else {
            CheckStock.OrderHasUnavailableItems(productIds)
        }
    }
}