package com.ing.baker.baas.recipe

import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.baas.recipe.Events.{ItemsReserved, ReserveItemsOutput}
import com.ing.baker.baas.recipe.Ingredients.{Item, OrderId, ReservedItems}
import com.ing.baker.baas.recipe.Interactions.ReserveItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ReserveItemsInstance(implicit timer: Timer[IO]) extends ReserveItems {

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] = {
      IO.sleep(100.millis)
        .as(ItemsReserved(ReservedItems(items, Array.fill(1)(Byte.MaxValue))))
        .unsafeToFuture()
  }
}

class FailingOnceReserveItemsInstance extends ReserveItems {

  var times = 1;

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] =
    if (times == 1) { times = times + 1; Future.failed(new RuntimeException("oups")) }
    else Future.successful(ItemsReserved(ReservedItems(items, Array.fill(1)(Byte.MaxValue))))
}

class FailingReserveItemsInstance extends ReserveItems {

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] =
    Future.failed(new RuntimeException("oups"))
}
