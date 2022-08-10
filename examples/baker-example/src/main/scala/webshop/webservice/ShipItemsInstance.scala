package webshop.webservice

import cats.effect.IO
import webshop.webservice.CheckoutFlowEvents.ShippingConfirmed
import webshop.webservice.CheckoutFlowIngredients.{ReservedItems, ShippingAddress}
import webshop.webservice.CheckoutFlowInteractions.ShipItems

import scala.concurrent.Future
import scala.concurrent.duration._
import cats.effect.Temporal

class ShipItemsInstance(implicit timer: Temporal[IO]) extends ShipItems {

  override def apply(shippingAddress: ShippingAddress, reservedItems: ReservedItems): Future[ShippingConfirmed] = {
      IO.sleep(500.millis)
        .as(ShippingConfirmed())
        .unsafeToFuture()
  }
}

