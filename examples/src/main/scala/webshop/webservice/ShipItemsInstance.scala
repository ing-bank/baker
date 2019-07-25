package webshop.webservice

import cats.effect.{IO, Timer}
import webshop.webservice.CheckoutFlowEvents.ShippingConfirmed
import webshop.webservice.CheckoutFlowIngredients.ShippingOrder
import webshop.webservice.CheckoutFlowInteractions.ShipItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ShipItemsInstance(implicit timer: Timer[IO]) extends ShipItems {

  override def apply(order: ShippingOrder): Future[ShippingConfirmed] = {
    IO.sleep(500 millis)
      .map(_ => ShippingConfirmed())
      .unsafeToFuture()
  }
}

