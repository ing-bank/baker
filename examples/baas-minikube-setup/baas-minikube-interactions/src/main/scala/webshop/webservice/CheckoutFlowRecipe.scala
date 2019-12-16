package webshop.webservice

import CheckoutFlowIngredients._
import CheckoutFlowEvents._

import scala.concurrent.Future

object CheckoutFlowIngredients {

  case class OrderId(orderId: String)

  case class Item(itemId: String)

  case class ReservedItems(items: List[Item], data: Array[Byte])

  case class ShippingAddress(address: String)

  case class PaymentInformation(info: String)

  case class ShippingOrder(items: List[Item], data: Array[Byte], address: ShippingAddress)
}

object CheckoutFlowEvents {

  case class OrderPlaced(orderId: OrderId, items: List[Item])

  case class PaymentInformationReceived(paymentInformation: PaymentInformation)

  case class ShippingAddressReceived(shippingAddress: ShippingAddress)

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[Item]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: ReservedItems) extends ReserveItemsOutput

  sealed trait MakePaymentOutput

  case class PaymentSuccessful(shippingOrder: ShippingOrder) extends MakePaymentOutput

  case class PaymentFailed() extends MakePaymentOutput

  case class ShippingConfirmed()
}

object CheckoutFlowInteractions {

  trait ReserveItems {

    def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput]
  }

  trait MakePayment {

    def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput]
  }

  trait ShipItems {

    def apply(order: ShippingOrder): Future[ShippingConfirmed]
  }
}
