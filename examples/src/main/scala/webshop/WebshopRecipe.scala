package webshop

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.baker.types._

object WebshopRecipe {


  PrimitiveValue(42).isInstanceOf(Int32)

  RecordValue(Map(
    "world" -> PrimitiveValue("!")
  )).isInstanceOf(
    RecordType(Seq(
      RecordField("world", CharArray)
    ))
  )

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
      name = "Order Placed",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )

    val OrderHadUnavailableItems: Event = Event(
      name = "Order Had Unavailable Items",
      providedIngredients = Seq(
        Ingredients.UnavailableItems
      ),
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
      name = "Reserve Items",
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
