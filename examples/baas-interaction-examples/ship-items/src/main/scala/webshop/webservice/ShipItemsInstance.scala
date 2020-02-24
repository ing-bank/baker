package webshop.webservice

import cats.effect.{IO, Timer}
import cats.implicits._

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._

class ShipItemsInstance(implicit context: ExecutionContext) extends ShipItems {

  implicit val timer: Timer[IO] = IO.timer(context)

  override def apply(order: ShippingOrder): Future[ShippingConfirmed] = {
      IO.sleep(500.millis)
        .as(ShippingConfirmed())
        .unsafeToFuture()
  }
}

