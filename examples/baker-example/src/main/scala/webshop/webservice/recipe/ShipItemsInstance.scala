package webshop.webservice.recipe

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import webshop.webservice.recipe.CheckoutFlowEvents.ShippingConfirmed
import webshop.webservice.recipe.CheckoutFlowIngredients.{ReservedItems, ShippingAddress}
import webshop.webservice.recipe.CheckoutFlowInteractions.ShipItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ShipItemsInstance() extends ShipItems {

  override def apply(shippingAddress: ShippingAddress, reservedItems: ReservedItems): Future[ShippingConfirmed] = {
      IO.sleep(500.millis)
        .as(ShippingConfirmed())
        .unsafeToFuture()
  }
}

