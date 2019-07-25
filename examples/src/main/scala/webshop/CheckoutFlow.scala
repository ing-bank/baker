package webshop

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

import scala.concurrent.duration._
import CheckoutFlow.models._
import CheckoutFlow.events._
import CheckoutFlow.interactions._

object CheckoutFlow {

  object models {

    case class OrderId(orderId: String)

    case class Item(itemId: String)

    case class ReservedItems(items: List[Item])

    case class ShippingAddress(address: String)

    case class PaymentInformation(info: String)

    case class ShippingOrder(items: List[Item], address: ShippingAddress)
  }

  object events {

    case class OrderPlaced(orderId: OrderId, items: List[Item])

    case class PaymentInformationReceived(info: PaymentInformation)

    case class ShippingAddressReceived(address: ShippingAddress)

    sealed trait ReserveItemsOutput
    case class OrderHadUnavailableItems(unavailableItems: List[Item]) extends ReserveItemsOutput
    case class ItemsReserved(reservedItems: List[Item]) extends ReserveItemsOutput

    sealed trait MakePaymentOutput
    case class PaymentSuccessful(order: ShippingOrder) extends MakePaymentOutput
    case class PaymentFailed() extends MakePaymentOutput

  }

  object interactions {

    val ReserveItems = Interaction(
      name = "ReserveItems",
      inputIngredients = Seq(
        Ingredient[OrderId]("orderId"),
        Ingredient[List[Item]]("items")
      ),
      output = Seq(
        Event[OrderHadUnavailableItems],
        Event[ItemsReserved]
      )
    )

    val MakePayment = Interaction(
      name = "MakePayment",
      inputIngredients = Seq(
        Ingredient[ReservedItems]("items"),
        Ingredient[ShippingAddress]("address"),
        Ingredient[PaymentInformation]("payment")
      ),
      output = Seq(
        Event[PaymentSuccessful],
        Event[PaymentFailed]
      )
    )
  }


  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[PaymentInformationReceived],
      Event[ShippingAddressReceived])
    .withInteractions(
      ReserveItems,
      MakePayment)
    .withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100 milliseconds)
        .withUntil(Some(UntilDeadline(24 hours)))
        .withMaxTimeBetweenRetries(Some(10 minutes))
        .build())
}
