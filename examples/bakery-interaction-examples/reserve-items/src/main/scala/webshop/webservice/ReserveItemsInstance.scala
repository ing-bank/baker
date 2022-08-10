package webshop.webservice

import cats.effect.IO
import com.typesafe.scalalogging.Logger

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}
import cats.effect.Temporal

class ReserveItemsInstance extends ReserveItems {

  private val log: Logger = Logger(classOf[ReserveItemsInstance])

  private val ctx: ExecutionContext = concurrent.ExecutionContext.Implicits.global
  private implicit val timer: Temporal[IO] = IO.timer(ctx)

  override def apply(items: List[Item]): Future[ReserveItemsOutput] = {
    log.info("Calling ReserveItems API")
    IO.sleep(1.second)
      .as(ItemsReserved(ReservedItems(items, Array.fill(1000)(Byte.MaxValue))))
      .unsafeToFuture()
  }
}