package com.ing.baker.test.recipe

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

trait ReserveItems {
  def apply(orderId: String, items: List[String]): Future[WebshopRecipe.ReserveItemsOutput]
}

class ReserveItemsInteraction extends ReserveItems {
  override def apply(orderId: String, items: List[String]): Future[WebshopRecipe.ReserveItemsOutput] = {
    val response: Future[Either[List[String], List[String]]] =
      Future.successful(Right(items))

    response.map {
      case Left(unavailableItems) =>
        WebshopRecipe.OrderHadUnavailableItems(unavailableItems)
      case Right(reservedItems) =>
        WebshopRecipe.ItemsReserved(reservedItems)
    }
  }
}
