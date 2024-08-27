package examples.scala.interactions

import scala.concurrent.Future
import scala.util.Random

trait CheckStockTrait {
  def apply(orderId: String, productIds: List[String]): Future[CheckStock.Outcome]
}

class CheckStockImpl extends CheckStockTrait {
  override def apply(orderId: String, productIds: List[String]): Future[CheckStock.Outcome] = {
    println(s"Checking stock for order: $orderId and products: $productIds")

    val randomNumber = new Random().nextInt(1000) + 1
    if (randomNumber < 500) {
      Future.successful(CheckStock.SufficientStock())
    } else {
      Future.successful(CheckStock.OrderHasUnavailableItems(productIds))
    }
  }
}
