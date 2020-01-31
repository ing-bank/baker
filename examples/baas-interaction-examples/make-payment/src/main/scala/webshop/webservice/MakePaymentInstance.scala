package webshop.webservice

import cats.effect.{IO, Timer}

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class MakePaymentInstance(implicit context: ExecutionContext) extends MakePayment {

  implicit val timer: Timer[IO] = IO.timer(context)

  override def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput] = {
    IO.sleep(5.second)
      .map(_ => println(Console.GREEN + processId + Console.RESET))
      .map(_ => PaymentSuccessful(ShippingOrder(items.items, items.data, address)))
      .unsafeToFuture()
  }
}

