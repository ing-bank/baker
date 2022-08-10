package webshop.webservice

import cats.effect.IO
import com.typesafe.scalalogging.Logger

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}
import cats.effect.Temporal

class ShipItemsInstance extends ShipItems {

  private val log: Logger = Logger(classOf[ShipItemsInstance])

  private val ctx: ExecutionContext = concurrent.ExecutionContext.Implicits.global

  private implicit val timer: Temporal[IO] = IO.timer(ctx)

  override def apply(shippingAddress: ShippingAddress, reservedItems: ReservedItems): Future[ShippingConfirmed] = {

    log.info("Calling ShimItems API")
    IO.sleep(500.millis)
      .as(ShippingConfirmed())
      .unsafeToFuture()
  }
}

