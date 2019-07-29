package webshop.webservice

import java.util.UUID

import cats.effect.{IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import webshop.webservice.CheckoutFlowIngredients.{Item, OrderId, PaymentInformation, ShippingAddress}

import scala.concurrent.ExecutionContext

object WebShopBaker {

  val checkoutFlowCompiledRecipe: CompiledRecipe =
    RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)

  def initRecipes(baker: Baker)(implicit time: Timer[IO], ec: ExecutionContext): IO[String] = {
    IO.fromFuture(IO(for {
      _ <- baker.addInteractionInstance(Seq(
        InteractionInstance.unsafeFrom(new ReserveItemsInstance()),
        InteractionInstance.unsafeFrom(new MakePaymentInstance()),
        InteractionInstance.unsafeFrom(new ShipItemsInstance())
      ))
      checkoutRecipeId <- baker.addRecipe(checkoutFlowCompiledRecipe)
      //_ = println("Adding Checkout Flow Recipe: ")
      //_ = println(checkoutFlowCompiledRecipe.getRecipeVisualization)
    } yield checkoutRecipeId))
  }
}

class WebShopBaker(baker: Baker, checkoutRecipeId: String)(implicit ec: ExecutionContext) extends WebShop {

  override def createCheckoutOrder(items: List[String]): IO[String] =
    IO.fromFuture(IO {
      val orderId: String = UUID.randomUUID().toString
      val event = EventInstance.unsafeFrom(
        CheckoutFlowEvents.OrderPlaced(OrderId(orderId), items.map(Item)))
      for {
        _ <- baker.bake(checkoutRecipeId, orderId)
        status <- baker.fireEventAndResolveWhenReceived(orderId, event)
        //_ = println(s"Order placed[$orderId]: $status")
      } yield orderId
    })

  override def addCheckoutAddressInfo(orderId: String, address: String): IO[Option[String]] =
    IO.fromFuture(IO {
      val event = EventInstance.unsafeFrom(
        CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress(address)))
      for {
        status <- baker.fireEventAndResolveWhenReceived(orderId, event)
        //_ = println(s"Add address [$orderId]: $status")
      } yield None
    })

  override def addCheckoutPaymentInfo(orderId: String, paymentInfo: String): IO[Option[String]] =
    IO.fromFuture(IO {
      val event = EventInstance.unsafeFrom(
        CheckoutFlowEvents.PaymentInformationReceived(PaymentInformation(paymentInfo)))
      for {
        status <- baker.fireEventAndResolveWhenReceived(orderId, event)
        //_ = println(s"Add payment [$orderId]: $status")
      } yield None
    })

  override def pollOrderStatus(orderId: String): IO[OrderStatus] =
    IO.fromFuture(IO {
      for {
        state <- baker.getRecipeInstanceState(orderId)
        /*
        _ = println
        _ = println("EVENTS")
        _ = state.events.foreach(println)
        _ = println
        _ = println("INGREDIENTS")
        _ = state.ingredients.foreach(println)
        */
        eventNames = state.events.map(_.name)
        status = {
          if(eventNames.contains("ShippingConfirmed"))
            OrderStatus.Complete
          else if(eventNames.contains("PaymentFailed"))
            OrderStatus.PaymentFailed
          else if(eventNames.contains("OrderHadUnavailableItems"))
            OrderStatus.UnavailableItems(state.ingredients("unavailableItems").as[List[Item]].map(_.itemId))
          else if(eventNames.containsSlice(List("ShippingAddressReceived", "PaymentInformationReceived")))
            OrderStatus.ProcessingPayment
          else if(eventNames.contains("PaymentSuccessful"))
            OrderStatus.ShippingItems
          else
            OrderStatus.InfoPending(List("ShippingAddressReceived", "PaymentInformationReceived")
              .filterNot(eventNames.contains)
              .map(_.replace("Received", "")))
        }
      } yield status
    })
}
