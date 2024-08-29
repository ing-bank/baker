package examples.scala.interactions

import examples.scala.ingredients.Address

import scala.concurrent.Future

trait ShipOrderTrait {
  def apply(orderId: String, address: Address): Future[ShipOrder.OrderShipped]
}

class ShipOrderImpl extends ShipOrderTrait {
  override def apply(orderId: String, address: Address): Future[ShipOrder.OrderShipped] = {
    println(s"Shipping order $orderId to $address")
    Future.successful(ShipOrder.OrderShipped())
  }
}
