package com.ing.bakery.baker.recipe

import cats.effect.{IO, Timer}
import com.ing.bakery.baker.recipe.Events.ReserveItemsOutput
import com.ing.bakery.baker.recipe.Ingredients.{Item, OrderId}
import com.ing.bakery.baker.recipe.Interactions.ReserveItems
import Events.ItemsReserved
import Ingredients.ReservedItems

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
