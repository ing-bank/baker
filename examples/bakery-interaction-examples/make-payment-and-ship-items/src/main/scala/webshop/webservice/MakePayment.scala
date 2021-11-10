package webshop.webservice

import com.ing.baker.recipe.annotations.FiresEvent

import scala.concurrent.Future

case class PaymentInformation(info: String)

sealed trait MakePaymentOutput

case class PaymentSuccessful() extends MakePaymentOutput

case class PaymentFailed() extends MakePaymentOutput

trait MakePayment {

  @FiresEvent(oneOf = Array(classOf[PaymentSuccessful], classOf[PaymentFailed]))
  def apply(processId: String, items: ReservedItems, payment: PaymentInformation): Future[MakePaymentOutput]
}