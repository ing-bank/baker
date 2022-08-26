package webshop.webservice.recipe

import cats.effect.{IO, Timer}
import webshop.webservice.recipe.CheckoutFlowEvents.ShippingConfirmed
import webshop.webservice.recipe.CheckoutFlowIngredients.{ReservedItems, ShippingAddress}
import webshop.webservice.recipe.CheckoutFlowInteractions.ShipItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ShipItemsInstance(implicit timer: Timer[IO]) extends ShipItems {

  override def apply(shippingAddress: ShippingAddress, reservedItems: ReservedItems): Future[ShippingConfirmed] = {
      IO.sleep(500.millis)
        .as(ShippingConfirmed())
        .unsafeToFuture()
  }
}

