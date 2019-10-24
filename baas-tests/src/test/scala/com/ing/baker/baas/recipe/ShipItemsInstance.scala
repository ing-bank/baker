package com.ing.baker.baas.recipe

import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.baas.recipe.CheckoutFlowEvents.ShippingConfirmed
import com.ing.baker.baas.recipe.CheckoutFlowIngredients.ShippingOrder
import com.ing.baker.baas.recipe.CheckoutFlowInteractions.ShipItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ShipItemsInstance(implicit timer: Timer[IO]) extends ShipItems {

  override def apply(order: ShippingOrder): Future[ShippingConfirmed] = {
      IO.sleep(500 millis)
        .as(ShippingConfirmed())
        .unsafeToFuture()
  }
}

