package examples.scala.events

import com.ing.baker.recipe.scaladsl.Event

object FraudCheckCompleted {
  val event: Event = Event(
    name = "FraudCheckCompleted",
    providedIngredients = Seq.empty,
    maxFiringLimit = Some(5)
  )
}
