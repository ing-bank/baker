package examples.scala.interactions

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction}
import examples.scala.ingredients.Address

object CancelOrder {

  val interaction: Interaction = Interaction(
    name = "CancelOrder",
    inputIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[List[String]](name = "unavailableProductIds")
    ),
    output = Seq(
      Event(
        name = "Success",
        providedIngredients = Seq.empty,
        maxFiringLimit = Some(1)
      )
    )
  )
}
