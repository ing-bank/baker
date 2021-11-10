package webshop.webservice

import cats.effect.{IO, Timer}
import com.typesafe.scalalogging.Logger

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class MakePaymentInstance extends MakePayment {

  val log: Logger = Logger(classOf[MakePaymentInstance])

  private val ctx: ExecutionContext = concurrent.ExecutionContext.Implicits.global
  private implicit val timer: Timer[IO] = IO.timer(ctx)

  override def apply(processId: String, items: ReservedItems, payment: PaymentInformation): Future[MakePaymentOutput] = {
    log.info("Calling MakePayments API")
    IO.sleep(1.second)
      .map(_ => PaymentSuccessful())
      .unsafeToFuture()
  }
}

