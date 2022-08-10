package webshop.webservice

import cats.effect.IO
import webshop.webservice.CheckoutFlowEvents.MakePaymentOutput
import webshop.webservice.CheckoutFlowIngredients.{PaymentInformation, ReservedItems, ShippingAddress, ShippingOrder}
import webshop.webservice.CheckoutFlowInteractions.MakePayment

import scala.concurrent.Future
import scala.concurrent.duration._
import cats.effect.Temporal

class MakePaymentInstance(implicit timer: Temporal[IO]) extends MakePayment {

  override def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput] = {
      IO.sleep(5.second)
        .map(_ => CheckoutFlowEvents.PaymentSuccessful())
        .unsafeToFuture()
  }
}
