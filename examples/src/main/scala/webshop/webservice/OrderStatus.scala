package webshop.webservice

import webshop.webservice.OrderStatus._

trait OrderStatus {

  override def toString: String = this match {
    case InfoPending(pending) => "info-pending:" + pending.mkString(",")
    case BadAddress => "bad-address"
    case PaymentFailed => "payment-failed"
    case ShippingAddress => "shipping-address"
    case Complete => "complete"
  }
}

object OrderStatus {

  case class InfoPending(pending: List[String]) extends OrderStatus

  case object BadAddress extends OrderStatus

  case object PaymentFailed extends OrderStatus

  case object ShippingAddress extends OrderStatus

  case object Complete extends OrderStatus
}
