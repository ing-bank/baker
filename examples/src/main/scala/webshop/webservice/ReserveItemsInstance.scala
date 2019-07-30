package webshop.webservice

import cats.implicits._
import cats.effect.{IO, Timer}
import webshop.webservice.CheckoutFlowEvents.ReserveItemsOutput
import webshop.webservice.CheckoutFlowIngredients.{Item, OrderId, ReservedItems}
import webshop.webservice.CheckoutFlowInteractions.ReserveItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ReserveItemsInstance(implicit timer: Timer[IO]) extends ReserveItems {

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] = {
    //(IO(println("Checking for items...")) *>
    IO.sleep(1 second)
      .map(_ => CheckoutFlowEvents.ItemsReserved(ReservedItems(items)))
      .unsafeToFuture()
  }
}
