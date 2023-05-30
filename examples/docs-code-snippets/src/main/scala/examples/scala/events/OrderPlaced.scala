package examples.scala.events

import com.ing.baker.recipe.scaladsl.{Event, Ingredient}

object OrderPlaced {
  val event: Event = Event(
    name = "OrderPlaced",
    providedIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[List[String]](name = "productIds"),
    ),
    maxFiringLimit = Some(1)
  )
}

