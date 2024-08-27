package examples.scala.interactions

import scala.concurrent.Future

trait CancelOrderTrait {
  def apply(orderId: String, unavailableProductIds: List[String]): Future[CancelOrder.OrderCancelled]
}

class CancelOrderImpl extends CancelOrderTrait {
  override def apply(orderId: String, unavailableProductIds: List[String]): Future[CancelOrder.OrderCancelled] = {
    println(s"Canceling order $orderId. The following products are unavailable: $unavailableProductIds")
    Future.successful(CancelOrder.OrderCancelled())
  }
}
