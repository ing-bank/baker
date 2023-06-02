package examples.scala.events

import com.ing.baker.recipe.scaladsl.{Event, Ingredient}
import examples.scala.ingredients.Address

object PaymentReceived {
  val event: Event = Event(
    name = "PaymentReceived",
    providedIngredients = Seq(
      Ingredient[String](name = "orderId"),
      Ingredient[BigDecimal](name = "amount"),
      Ingredient[String](name = "currency")
    ),
    maxFiringLimit = Some(1)
  )
}
