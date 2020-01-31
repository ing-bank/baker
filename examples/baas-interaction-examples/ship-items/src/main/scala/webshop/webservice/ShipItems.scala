package webshop.webservice

import scala.concurrent.Future


case class Item(itemId: String)

case class ShippingAddress(address: String)

case class ShippingOrder(items: List[Item], data: Array[Byte], address: ShippingAddress)

case class ShippingConfirmed()


trait ShipItems {

  def apply(order: ShippingOrder): Future[ShippingConfirmed]
}