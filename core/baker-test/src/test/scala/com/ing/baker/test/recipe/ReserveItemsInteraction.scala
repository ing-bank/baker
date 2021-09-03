package com.ing.baker.test.recipe

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

trait ReserveItems {
  def apply(orderId: String, items: List[String]): Future[WebshopRecipe.ReserveItemsOutput]
}

class ReserveItemsInteraction extends ReserveItems {
  override def apply(orderId: String, items: List[String]): Future[WebshopRecipe.ReserveItemsOutput] = {
    // Http call to the Warehouse service
    val response: Future[Either[List[String], List[String]]] =
    // This is mocked for the sake of the example
      Future.successful(Right(items))

    // Build an event instance that Baker understands
    response.map {
      case Left(unavailableItems) =>
        WebshopRecipe.OrderHadUnavailableItems(unavailableItems)
      case Right(reservedItems) =>
        WebshopRecipe.ItemsReserved(reservedItems)
    }
  }
}
