package webshop.webservice

import scala.concurrent.Future

case class PaymentInformation(info: String)

sealed trait MakePaymentOutput

case class PaymentSuccessful() extends MakePaymentOutput

case class PaymentFailed() extends MakePaymentOutput

trait MakePayment {

  def apply(processId: String, items: ReservedItems, payment: PaymentInformation): Future[MakePaymentOutput]
}