package webshop.webservice

import scala.concurrent.Future

case class Item(itemId: String)

case class ShippingAddress(address: String)

case class PaymentInformation(info: String)

sealed trait MakePaymentOutput

case class ShippingOrder(items: List[Item], data: Array[Byte], address: ShippingAddress)

case class ReservedItems(items: List[Item], data: Array[Byte])

case class PaymentSuccessful(shippingOrder: ShippingOrder) extends MakePaymentOutput

case class PaymentFailed() extends MakePaymentOutput

trait MakePayment {

  def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput]
}