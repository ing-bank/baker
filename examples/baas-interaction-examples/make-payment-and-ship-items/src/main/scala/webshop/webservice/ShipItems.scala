package webshop.webservice

import scala.concurrent.Future

case class ShippingConfirmed()

trait ShipItems {

  def apply(order: ShippingOrder): Future[ShippingConfirmed]
}