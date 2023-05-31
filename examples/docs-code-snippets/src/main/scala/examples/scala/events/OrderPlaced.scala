package examples.scala.events

import com.ing.baker.recipe.scaladsl.{Event, Ingredient}
import examples.scala.ingredients.Address

object OrderPlaced {
  val event: Event = Event(
    name = "OrderPlaced",
    providedIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[String](name = "customerId"),
      Ingredient[Address](name = "address"),
      Ingredient[List[String]](name = "productIds"),
    ),
    maxFiringLimit = Some(1)
  )
}
