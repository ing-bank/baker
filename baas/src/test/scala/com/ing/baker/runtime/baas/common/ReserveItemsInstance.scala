package com.ing.baker.runtime.baas.common

import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.runtime.baas.common.CheckoutFlowEvents.ReserveItemsOutput
import com.ing.baker.runtime.baas.common.CheckoutFlowIngredients.{Item, OrderId, ReservedItems}
import com.ing.baker.runtime.baas.common.CheckoutFlowInteractions.ReserveItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ReserveItemsInstance(implicit timer: Timer[IO]) extends ReserveItems {

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] = {
      IO.sleep(1 second)
        .as(CheckoutFlowEvents.ItemsReserved(ReservedItems(items, Array.fill(1000)(Byte.MaxValue))))
        .unsafeToFuture()
  }
}
