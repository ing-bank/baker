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
      Ingredient[String]("order-id")

    val Items: Ingredient[List[String]] =
      Ingredient[List[String]]("items")

    val ReservedItems: Ingredient[List[String]] =
      Ingredient[List[String]]("reserved-items")

    val MissingItems: Ingredient[List[String]] =
      Ingredient[List[String]]("missing-items")
  }

  object Events {

    val OrderPlaced: Event = Event(
      name = "order-placed",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )

    val OrderHadMissingItems: Event = Event(
      name = "Order Had Missing Items",
      providedIngredients = Seq.empty,
      maxFiringLimit = Some(1)
    )

    val ItemsReserved: Event = Event(
      name = "Items Reserved",
      providedIngredients = Seq(
        Ingredients.ReservedItems
      ),
      maxFiringLimit = Some(1)
    )
  }

  object Interactions {

    val ReserveItems: Interaction = Interaction(
      name = "validate-order",
      inputIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items,
      ),
      output = Seq(
        Events.OrderHadMissingItems,
        Events.ItemsReserved
      )
    )
  }
}
