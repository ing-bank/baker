package com.ing.baker.baas.recipe

import cats.effect.{IO, Timer}
import com.ing.baker.baas.recipe.Events.MakePaymentOutput
import com.ing.baker.baas.recipe.Ingredients.{PaymentInformation, ReservedItems, ShippingAddress, ShippingOrder}
import com.ing.baker.baas.recipe.Interactions.MakePayment

import scala.concurrent.Future
import scala.concurrent.duration._

class MakePaymentInstance(implicit timer: Timer[IO]) extends MakePayment {

  override def apply(items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput] = {
      IO.sleep(5.second)
        .map(_ => Events.PaymentSuccessful(ShippingOrder(items.items, items.data, address)))
        .unsafeToFuture()
  }
}
