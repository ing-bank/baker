package webshop.webservice.recipe

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import webshop.webservice.recipe.CheckoutFlowEvents.ReserveItemsOutput
import webshop.webservice.recipe.CheckoutFlowIngredients.{Item, ReservedItems}
import webshop.webservice.recipe.CheckoutFlowInteractions.ReserveItems

import scala.concurrent.Future
import scala.concurrent.duration._

class ReserveItemsInstance() extends ReserveItems {

  override def apply(items: List[Item]): Future[ReserveItemsOutput] = {
      IO.sleep(1.second)
        .as(CheckoutFlowEvents.ItemsReserved(ReservedItems(items, Array.fill(1000)(Byte.MaxValue))))
        .unsafeToFuture()
  }
}
