package webshop.webservice

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import com.typesafe.scalalogging.Logger

import scala.concurrent.Future
import scala.concurrent.duration._

class MakePaymentInstance extends MakePayment {

  val log: Logger = Logger(classOf[MakePaymentInstance])

  override def apply(processId: String, items: ReservedItems, payment: PaymentInformation): Future[MakePaymentOutput] = {
    log.info("Calling MakePayments API")
    IO.sleep(1.second)
      .map(_ => PaymentSuccessful())
      .unsafeToFuture()
  }
}

