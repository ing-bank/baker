package webshop.webservice

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import com.typesafe.scalalogging.Logger

import scala.concurrent.duration._
import scala.concurrent.Future

class ReserveItemsInstance extends ReserveItems {

  private val log: Logger = Logger(classOf[ReserveItemsInstance])

  override def apply(items: List[Item]): Future[ReserveItemsOutput] = {
    log.info("Calling ReserveItems API")
    IO.sleep(1.second)
      .as(ItemsReserved(ReservedItems(items, Array.fill(1000)(Byte.MaxValue))))
      .unsafeToFuture()
  }
}