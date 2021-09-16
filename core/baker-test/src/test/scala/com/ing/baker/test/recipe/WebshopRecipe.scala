package com.ing.baker.test.recipe

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.baker.test.{EmptyFlow, EventsFlow}

import scala.language.postfixOps

object WebshopRecipe {

  case class OrderPlaced(orderId: String, items: List[String])

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

  val ReserveItems: Interaction = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
      Ingredient[String]("orderId"),
      Ingredient[List[String]]("items")
    ),
    output = Seq(
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
  )

  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced])
    .withInteractions(
      ReserveItems)

  val happyFlow: EventsFlow =
    classOf[OrderPlaced] ::
      classOf[ItemsReserved] ::
      EmptyFlow
}
