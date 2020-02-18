package webshop.webservice

import cats.effect.{IO, Timer}
import cats.implicits._

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._

class ReserveItemsInstance()(implicit context: ExecutionContext) extends ReserveItems {
  implicit val timer: Timer[IO] = IO.timer(context)

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] = {
      IO.sleep(1.second)
        .as(ItemsReserved(ReservedItems(items, Array.fill(1000)(Byte.MaxValue))))
        .unsafeToFuture()
  }
}