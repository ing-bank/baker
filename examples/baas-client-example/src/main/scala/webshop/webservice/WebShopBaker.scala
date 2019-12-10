package webshop.webservice

import java.util.UUID

import cats.effect.{IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import com.typesafe.scalalogging.LazyLogging
import webshop.webservice.CheckoutFlowIngredients.{Item, OrderId, PaymentInformation, ShippingAddress}

import scala.concurrent.{ExecutionContext, Future}

object WebShopBaker extends LazyLogging {

  val checkoutFlowCompiledRecipe: CompiledRecipe =
    RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)

  def initRecipes(baker: Baker)(implicit time: Timer[IO], ec: ExecutionContext): IO[String] = {
    IO.fromFuture(IO(for {
      checkoutRecipeId <- baker.addRecipe(checkoutFlowCompiledRecipe)
      _ = println(Console.GREEN + "V3 Checkout Recipe ID :: " + checkoutRecipeId + Console.RESET)
    } yield checkoutRecipeId))
  }
}

class WebShopBaker(baker: Baker, checkoutRecipeId: String)(implicit ec: ExecutionContext) extends WebShop {

  import WebShopBaker.logger

  override def createCheckoutOrder(items: List[String]): IO[String] =
    IO.fromFuture(IO {
      val orderId: String = UUID.randomUUID().toString
      val event = EventInstance.unsafeFrom(
        CheckoutFlowEvents.OrderPlaced(OrderId(orderId), items.map(Item)))
      for {
        _ <- baker.bake(checkoutRecipeId, orderId)
        status <- baker.fireEventAndResolveWhenReceived(orderId, event)
        _ = logger.info(s"${event.name}[$orderId]: $status")
      } yield orderId
    })

  override def addCheckoutAddressInfo(orderId: String, address: String): IO[Option[String]] =
    IO.fromFuture(IO {
      fireAndInformEvent(orderId, EventInstance.unsafeFrom(
        CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress(address))))
    })

  override def addCheckoutPaymentInfo(orderId: String, paymentInfo: String): IO[Option[String]] =
    IO.fromFuture(IO {
      fireAndInformEvent(orderId, EventInstance.unsafeFrom(
        CheckoutFlowEvents.PaymentInformationReceived(PaymentInformation(paymentInfo))))
    })

  private def fireAndInformEvent(orderId: String, event: EventInstance): Future[Option[String]] = {
    for {
      status <- baker.fireEventAndResolveWhenReceived(orderId, event)
      _ = logger.info(s"${event.name}[$orderId]: $status")
    } yield None
  }

  override def pollOrderStatus(orderId: String): IO[OrderStatus] =
    IO.fromFuture(IO {
      for {
        state <- baker.getRecipeInstanceState(orderId)
        eventNames = state.events.map(_.name)
        status = {
          if (eventNames.contains("ShippingConfirmed"))
            OrderStatus.Complete
          else if (eventNames.contains("PaymentFailed"))
            OrderStatus.PaymentFailed
          else if (eventNames.contains("OrderHadUnavailableItems"))
            OrderStatus.UnavailableItems(state.ingredients("unavailableItems").as[List[Item]].map(_.itemId))
          else if (eventNames.containsSlice(List("ShippingAddressReceived", "PaymentInformationReceived")))
            OrderStatus.ProcessingPayment
          else if (eventNames.contains("PaymentSuccessful"))
            OrderStatus.ShippingItems
          else
            OrderStatus.InfoPending(List("ShippingAddressReceived", "PaymentInformationReceived")
              .filterNot(eventNames.contains)
              .map(_.replace("Received", "")))
        }
      } yield status
    })

  override def gracefulShutdown: IO[Unit] =
    IO {
      baker.gracefulShutdown()
    }
}
