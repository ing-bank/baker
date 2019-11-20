package webshop.webservice

import cats.effect.{IO, Timer}
import webshop.webservice.CheckoutFlowEvents.MakePaymentOutput
import webshop.webservice.CheckoutFlowIngredients.{PaymentInformation, ReservedItems, ShippingAddress, ShippingOrder}
import webshop.webservice.CheckoutFlowInteractions.MakePayment

import scala.concurrent.Future
import scala.concurrent.duration._

class MakePaymentInstance(implicit timer: Timer[IO]) extends MakePayment {

  override def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput] = {
      IO.sleep(5 second)
        .map(_ => println(Console.GREEN + processId + Console.RESET))
        .map(_ => CheckoutFlowEvents.PaymentSuccessful(ShippingOrder(items.items, items.data, address)))
        .unsafeToFuture()
  }
}
