package webshop.webservice

import cats.effect.{IO, Timer}
import cats.implicits._

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class ShipItemsInstance extends ShipItems {
  private val ctx: ExecutionContext = concurrent.ExecutionContext.Implicits.global

  private implicit val timer: Timer[IO] = IO.timer(ctx)

  override def apply(order: ShippingOrder): Future[ShippingConfirmed] = {
    IO.sleep(500.millis)
      .as(ShippingConfirmed())
      .unsafeToFuture()
  }
}

