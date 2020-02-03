package com.ing.baker.baas.test

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import CheckoutFlowIngredients._
import CheckoutFlowEvents._
import CheckoutFlowInteractions._
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilMaximumRetries

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

  def ReserveItemsInteraction = Interaction(
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

    def apply(processId: String, items: ReservedItems, address: ShippingAddress, payment: PaymentInformation): Future[MakePaymentOutput]
  }

  def MakePaymentInteraction = Interaction(
    name = "MakePayment",
    inputIngredients = Seq(
      com.ing.baker.recipe.scaladsl.recipeInstanceId,
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

  def ShipItemsInteraction = Interaction(
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

  def recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[PaymentInformationReceived],
      Event[ShippingAddressReceived])
    .withInteractions(
      ReserveItemsInteraction,
      MakePaymentInteraction,
      ShipItemsInteraction)
    .withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(1.second)
        .withUntil(Some(UntilMaximumRetries(5)))
        .build())
}
