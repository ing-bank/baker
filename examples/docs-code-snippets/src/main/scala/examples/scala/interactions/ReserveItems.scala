package examples.scala.interactions

import com.ing.baker.recipe.scaladsl.{Ingredient, Interaction}

trait ReserveItems extends Interaction {

  sealed trait Outcome

  case class OrderHasUnavailableItems(unavailableProductIds: List[String]) extends Outcome

  object Success extends Outcome

  val reserve: Interaction = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[List[String]](name = "productIds")
    ),
    output = Seq(

    )
  )

}
