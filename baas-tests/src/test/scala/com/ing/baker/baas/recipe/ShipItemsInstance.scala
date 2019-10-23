package com.ing.baker.runtime.baas.common

import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.runtime.baas.common.CheckoutFlowEvents.ShippingConfirmed
import com.ing.baker.runtime.baas.common.CheckoutFlowIngredients.ShippingOrder
import com.ing.baker.runtime.baas.common.CheckoutFlowInteractions.ShipItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ShipItemsInstance(implicit timer: Timer[IO]) extends ShipItems {

  override def apply(order: ShippingOrder): Future[ShippingConfirmed] = {
      IO.sleep(500 millis)
        .as(ShippingConfirmed())
        .unsafeToFuture()
  }
}

