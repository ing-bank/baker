package examples.kotlin.interactions

import examples.kotlin.ingredients.Address

object ShipOrderImpl : ShipOrder {
    override fun apply(orderId: String, address: Address): ShipOrder.Success {
        println("Shipping order $orderId to $address")
        return ShipOrder.Success
    }
}