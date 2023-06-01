package examples.scala.interactions

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction}
import examples.scala.ingredients.Address

object ShipOrder {

  val interaction: Interaction = Interaction(
    name = "ShipOrder",
    inputIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[Address](name = "address")
    ),
    output = Seq(
      Event(
        name = "OrderShipped",
        providedIngredients = Seq.empty,
        maxFiringLimit = Some(1)
      )
    )
  )
}
