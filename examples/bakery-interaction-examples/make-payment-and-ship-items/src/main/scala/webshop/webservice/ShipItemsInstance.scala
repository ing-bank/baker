package webshop.webservice

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import com.typesafe.scalalogging.Logger

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class ShipItemsInstance extends ShipItems {

  private val log: Logger = Logger(classOf[ShipItemsInstance])

  override def apply(shippingAddress: ShippingAddress, reservedItems: ReservedItems): Future[ShippingConfirmed] = {

    log.info("Calling ShimItems API")
    IO.sleep(500.millis)
      .as(ShippingConfirmed())
      .unsafeToFuture()
  }
}

