package com.ing.bakery.recipe

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, RetryWithIncrementalBackoff}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.bakery.recipe.Events.{ItemsReserved, OrderHadUnavailableItems, OrderPlaced, ReserveItemsOutput}

import scala.collection.immutable.Seq
import scala.concurrent.Future
import scala.concurrent.duration._

object Ingredients {

  case class OrderId(orderId: String)

  case class Item(itemId: String)

  case class ReservedItems(items: List[Item], data: Array[Byte])

}

object Events {

  case class OrderPlaced(orderId: Ingredients.OrderId, items: List[Ingredients.Item])

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[Ingredients.Item]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: Ingredients.ReservedItems) extends ReserveItemsOutput

  case class ItemsReservationCanceled(reservedItems: Ingredients.ReservedItems) extends ReserveItemsOutput

}

object Interactions {

  trait ReserveItems {

    def apply(orderId: Ingredients.OrderId, items: List[Ingredients.Item]): Future[ReserveItemsOutput]
  }

  def ReserveItemsInteraction: Interaction = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
      Ingredient[Ingredients.OrderId]("orderId"),
      Ingredient[List[Ingredients.Item]]("items")
    ),
    output = Seq(
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
  )

  trait CancelReserveItems {

    def apply(orderId: Ingredients.OrderId, items: List[Ingredients.Item]): Future[ReserveItemsOutput]
  }

  def CancelReserveItemsInteraction: Interaction = Interaction(
    name = "CancelReserveItems",
    inputIngredients = Seq(
      Ingredient[Ingredients.OrderId]("orderId")
    ),
    output = Seq(
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
  )
}

object ItemReservationRecipe {

  private def recipeBase = Recipe("ItemReservation.recipe")
    .withSensoryEvents(
      Event[OrderPlaced])
    .withInteractions(
      Interactions.ReserveItemsInteraction)

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

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)

  val compiledRecipeWithBlockingStrategy: CompiledRecipe = RecipeCompiler.compileRecipe(recipeWithBlockingStrategy)
}
