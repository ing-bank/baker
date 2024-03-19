package examples.scala.interactions

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction}

object CheckStock {

  sealed trait Outcome

  case class SufficientStock() extends Outcome
  case class OrderHasUnavailableItems(unavailableProductIds: List[String]) extends Outcome

  val interaction: Interaction = Interaction(
    name = "CheckStock",
    inputIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[List[String]](name = "productIds")
    ),
    output = Seq(
      Event[SufficientStock],
      Event[OrderHasUnavailableItems]
    )
  )
}
