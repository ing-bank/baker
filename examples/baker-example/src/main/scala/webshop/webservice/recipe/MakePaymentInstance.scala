package webshop.webservice.recipe

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import webshop.webservice.recipe.CheckoutFlowEvents.MakePaymentOutput
import webshop.webservice.recipe.CheckoutFlowIngredients.{PaymentInformation, ReservedItems}
import webshop.webservice.recipe.CheckoutFlowInteractions.MakePayment

import scala.concurrent.Future
import scala.concurrent.duration._

class MakePaymentInstance() extends MakePayment {

  override def apply(processId: String, items: ReservedItems, payment: PaymentInformation): Future[MakePaymentOutput] = {
      IO.sleep(5.second)
        .map(_ => CheckoutFlowEvents.PaymentSuccessful())
        .unsafeToFuture()
  }
}
