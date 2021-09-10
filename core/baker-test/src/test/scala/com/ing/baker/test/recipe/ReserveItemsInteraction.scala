package com.ing.baker.test.recipe

import com.ing.baker.recipe.annotations.{AsyncInteraction, FiresEvent}
import com.ing.baker.test.recipe.WebshopRecipe.{ItemsReserved, OrderHadUnavailableItems}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

trait ReserveItems {
  def apply(orderId: String, items: List[String]): Future[WebshopRecipe.ReserveItemsOutput]
}

class ReserveItemsInteraction extends ReserveItems {
  override def apply(orderId: String, items: List[String]): Future[WebshopRecipe.ReserveItemsOutput] = {
    println(s"!!!!!!! ${orderId} ${items}")
    // Http call to the Warehouse service
    val response: Future[Either[List[String], List[String]]] =
    // This is mocked for the sake of the example
      Future.successful(Right(items))

    // Build an event instance that Baker understands
    val ev = response.map {
      case Left(unavailableItems) =>
        WebshopRecipe.OrderHadUnavailableItems(unavailableItems)
      case Right(reservedItems) =>
        WebshopRecipe.ItemsReserved(reservedItems)
    }
    ev.map(println)
    ev;
  }
}
