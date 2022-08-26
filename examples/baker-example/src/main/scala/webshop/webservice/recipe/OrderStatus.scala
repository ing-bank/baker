package webshop.webservice.recipe

import webshop.webservice.recipe.OrderStatus._

trait OrderStatus {

  override def toString: String = this match {
    case InfoPending(pending) => "info-pending:" + pending.mkString(",")
    case UnavailableItems(items) => "unavailable-items:" + items.length
    case PaymentFailed => "payment-failed"
    case ShippingItems => "shipping-items"
    case ProcessingPayment => "processing-payment"
    case Complete => "complete"
  }
}

object OrderStatus {

  case class InfoPending(pending: List[String]) extends OrderStatus

  case class UnavailableItems(items: List[String]) extends OrderStatus

  case object PaymentFailed extends OrderStatus

  case object ShippingItems extends OrderStatus

  case object ProcessingPayment extends OrderStatus

  case object Complete extends OrderStatus
}
