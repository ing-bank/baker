package examples.scala.interactions

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction}

object CheckStock {

  val success: Event = Event(
    name = "SufficientStock",
    providedIngredients = Seq.empty,
    maxFiringLimit = Some(1)
  )

  val orderHasUnavailableItems: Event = Event(
    name = "OrderHasUnavailableItems",
    providedIngredients = Seq(
      Ingredient[List[String]](name = "unavailableProductIds")
    ),
    maxFiringLimit = Some(1)
  )

  val interaction: Interaction = Interaction(
    name = "CheckStock",
    inputIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[List[String]](name = "productIds")
    ),
    output = Seq(
      success,
      orderHasUnavailableItems
    )
  )
}
