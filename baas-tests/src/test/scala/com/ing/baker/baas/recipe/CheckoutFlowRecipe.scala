package com.ing.baker.baas.recipe

import com.ing.baker.baas.recipe.Events._
import com.ing.baker.baas.recipe.Ingredients._
import com.ing.baker.baas.recipe.Interactions._
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, RetryWithIncrementalBackoff}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

import scala.concurrent.Future
import scala.concurrent.duration._

object CheckoutFlowIngredients {

  case class OrderId(orderId: String)

  case class Item(itemId: String)

  case class ReservedItems(items: List[Item], data: Array[Byte])

  case class ShippingAddress(address: String)

  case class PaymentInformation(info: String)

  case class ShippingOrder(items: List[Item], data: Array[Byte], address: ShippingAddress)

}

object CheckoutFlowEvents {

  case class OrderPlaced(orderId: OrderId, items: List[Item])

  case class PaymentInformationReceived(paymentInformation: PaymentInformation)

  case class ShippingAddressReceived(shippingAddress: ShippingAddress)

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[Item]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: ReservedItems) extends ReserveItemsOutput

  sealed trait MakePaymentOutput

  case class PaymentSuccessful(shippingOrder: ShippingOrder) extends MakePaymentOutput

  case class PaymentFailed() extends MakePaymentOutput

  case class ShippingConfirmed()

}

object CheckoutFlowInteractions {

  trait ReserveItems {

    def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput]
  }

  def ReserveItemsInteraction: Interaction = Interaction(
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

  trait MakePayment {

    def apply(items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput]
  }

  def MakePaymentInteraction: Interaction = Interaction(
    name = "MakePayment",
    inputIngredients = Seq(
      Ingredient[ReservedItems]("reservedItems"),
      Ingredient[ShippingAddress]("shippingAddress"),
      Ingredient[PaymentInformation]("paymentInformation")
    ),
    output = Seq(
      Event[PaymentSuccessful],
      Event[PaymentFailed]
    )
  )

  trait ShipItems {

    def apply(order: ShippingOrder): Future[ShippingConfirmed]
  }

  def ShipItemsInteraction: Interaction = Interaction(
    name = "ShipItems",
    inputIngredients = Seq(
      Ingredient[ShippingOrder]("shippingOrder")
    ),
    output = Seq(
      Event[ShippingConfirmed]
    )
  )
}

object CheckoutFlowRecipe {

  private def recipeBase = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[PaymentInformationReceived],
      Event[ShippingAddressReceived])
    .withInteractions(
      ReserveItemsInteraction,
      MakePaymentInteraction,
      ShipItemsInteraction)

  def recipe: Recipe =
    recipeBase.withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100.milliseconds)
        .withUntil(Some(UntilDeadline(24.hours)))
        .withMaxTimeBetweenRetries(Some(10.minutes))
        .build())

  def recipeWithBlockingStrategy: Recipe =
    recipeBase.withDefaultFailureStrategy(
      BlockInteraction())
}
