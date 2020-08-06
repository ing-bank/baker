package webshop.webservice

import java.util.UUID

import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import com.typesafe.scalalogging.LazyLogging
import webshop.webservice.CheckoutFlowIngredients.{Item, OrderId, PaymentInformation, ShippingAddress}

object WebShopBaker {

  val checkoutFlowCompiledRecipe: CompiledRecipe =
    RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
}

class WebShopBaker(baker: Baker, checkoutRecipeId: String)(implicit cs: ContextShift[IO]) extends WebShop with LazyLogging {

  override def listRecipeNames: IO[List[String]] =
    IO.fromFuture(IO(baker.getAllRecipes)).map(_.values.toList.map(_.compiledRecipe.name))

  override def createCheckoutOrder(items: List[String]): IO[String] = {
    val orderId: String = UUID.randomUUID().toString
    val event = EventInstance.unsafeFrom(
      CheckoutFlowEvents.OrderPlaced(OrderId(orderId), items.map(Item)))
    for {
      _ <- IO.fromFuture(IO(baker.bake(checkoutRecipeId, orderId)))
      status <- IO.fromFuture(IO(baker.fireEventAndResolveWhenReceived(orderId, event)))
      _ = logger.info(s"${event.name}[$orderId]: $status")
    } yield orderId
  }

  override def addCheckoutAddressInfo(orderId: String, address: String): IO[Unit] =
    fireAndInformEvent(orderId, EventInstance.unsafeFrom(
      CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress(address))))

  override def addCheckoutPaymentInfo(orderId: String, paymentInfo: String): IO[Unit] =
    fireAndInformEvent(orderId, EventInstance.unsafeFrom(
      CheckoutFlowEvents.PaymentInformationReceived(PaymentInformation(paymentInfo))))

  private def fireAndInformEvent(orderId: String, event: EventInstance): IO[Unit] = {
    IO.fromFuture(IO {
      baker.fireEventAndResolveWhenReceived(orderId, event)
    }).void
  }

  override def pollOrderStatus(orderId: String): IO[OrderStatus] =
    for {
      state <- IO.fromFuture(IO(baker.getRecipeInstanceState(orderId)))
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

  override def gracefulShutdown: IO[Unit] =
    IO {
      baker.gracefulShutdown()
    }
}
