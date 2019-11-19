package com.ing.baker.baas.recipe

import cats.effect.{IO, Timer}
import com.ing.baker.baas.recipe.CheckoutFlowEvents.MakePaymentOutput
import com.ing.baker.baas.recipe.CheckoutFlowIngredients.{PaymentInformation, ReservedItems, ShippingAddress, ShippingOrder}
import com.ing.baker.baas.recipe.CheckoutFlowInteractions.MakePayment

import scala.concurrent.Future
import scala.concurrent.duration._

class MakePaymentInstance(implicit timer: Timer[IO]) extends MakePayment {

  override def apply(items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput] = {
      IO.sleep(5 second)
        .map(_ => CheckoutFlowEvents.PaymentSuccessful(ShippingOrder(items.items, items.data, address)))
        .unsafeToFuture()
  }
}
