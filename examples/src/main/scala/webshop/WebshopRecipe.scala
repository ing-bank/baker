package webshop

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

object WebshopRecipe {

  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Events.OrderPlaced
    )
    .withInteractions(
      Interactions.ReserveItems,
    )

  object Ingredients {

    val OrderId: Ingredient[String] =
      Ingredient[String]("orderId")

    val Items: Ingredient[List[String]] =
      Ingredient[List[String]]("items")

    val ReservedItems: Ingredient[List[String]] =
      Ingredient[List[String]]("reservedItems")

    val UnavailableItems: Ingredient[List[String]] =
      Ingredient[List[String]]("unavailableItems")
  }

  object Events {

    val OrderPlaced: Event = Event(
      name = "OrderPlaced",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )

    val OrderHadUnavailableItems: Event = Event(
      name = "OrderHadUnavailableItems",
      providedIngredients = Seq(
        Ingredients.UnavailableItems
      ),
      maxFiringLimit = Some(1)
    )

    val ItemsReserved: Event = Event(
      name = "ItemsReserved",
      providedIngredients = Seq(
        Ingredients.ReservedItems
      ),
      maxFiringLimit = Some(1)
    )
  }

  object Interactions {

    val ReserveItems: Interaction = Interaction(
      name = "ReserveItems",
      inputIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items,
      ),
      output = Seq(
        Events.OrderHadUnavailableItems,
        Events.ItemsReserved
      )
    )
  }
}
