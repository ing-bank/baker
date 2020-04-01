package webshop.webservice

import cats.effect.{IO, Timer}

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class MakePaymentInstance extends MakePayment {

  private val ctx: ExecutionContext = concurrent.ExecutionContext.Implicits.global
  private implicit val timer: Timer[IO] = IO.timer(ctx)

  override def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput] = {
    IO.sleep(1.second)
      .map(_ => println(Console.GREEN + processId + Console.RESET))
      .map(_ => PaymentSuccessful(ShippingOrder(items.items, items.data, address)))
      .unsafeToFuture()
  }
}

