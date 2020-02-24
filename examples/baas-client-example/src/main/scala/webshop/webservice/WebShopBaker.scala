package webshop.webservice

import java.util.UUID

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import com.typesafe.scalalogging.LazyLogging
import webshop.webservice.CheckoutFlowIngredients.{Item, OrderId, PaymentInformation, ShippingAddress}

import scala.concurrent.{ExecutionContext, Future}

object WebShopBaker {

  val checkoutFlowCompiledRecipe: CompiledRecipe =
    RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)

  def initRecipes(baker: Baker)(implicit time: Timer[IO], cs: ContextShift[IO]): IO[String] =
    IO.fromFuture(IO(baker.addRecipe(checkoutFlowCompiledRecipe)))
}

class WebShopBaker(baker: Baker, checkoutRecipeId: String)(implicit cs: ContextShift[IO], ec: ExecutionContext) extends WebShop with LazyLogging {

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

  override def addCheckoutAddressInfo(orderId: String, address: String): IO[Unit] =
    IO.fromFuture(IO {
      fireAndInformEvent(orderId, EventInstance.unsafeFrom(
        CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress(address))))
    })

  override def addCheckoutPaymentInfo(orderId: String, paymentInfo: String): IO[Unit] =
    IO.fromFuture(IO {
      fireAndInformEvent(orderId, EventInstance.unsafeFrom(
        CheckoutFlowEvents.PaymentInformationReceived(PaymentInformation(paymentInfo))))
    })

  private def fireAndInformEvent(orderId: String, event: EventInstance): Future[Unit] = {
    for {
      status <- baker.fireEventAndResolveWhenReceived(orderId, event)
      _ = logger.info(s"${event.name}[$orderId]: $status")
    } yield ()
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
