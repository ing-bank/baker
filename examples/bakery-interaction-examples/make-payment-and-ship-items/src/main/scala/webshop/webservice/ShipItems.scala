package webshop.webservice

import scala.concurrent.Future

case class Item(itemId: String)

case class ShippingConfirmed()

case class ShippingAddress(address: String)

case class ReservedItems(items: List[Item], data: Array[Byte])

trait ShipItems {

  def apply(shippingAddress: ShippingAddress, reservedItems: ReservedItems): Future[ShippingConfirmed]
}