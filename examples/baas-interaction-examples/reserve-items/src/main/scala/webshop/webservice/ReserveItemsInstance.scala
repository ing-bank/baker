package webshop.webservice

import cats.effect.{IO, Timer}
import cats.implicits._

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class ReserveItemsInstance extends ReserveItems {
  private val ctx: ExecutionContext = concurrent.ExecutionContext.Implicits.global
  private implicit val timer: Timer[IO] = IO.timer(ctx)

  override def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput] = {
    IO.sleep(1.second)
      .as(ItemsReserved(ReservedItems(items, Array.fill(1000)(Byte.MaxValue))))
      .unsafeToFuture()
  }
}