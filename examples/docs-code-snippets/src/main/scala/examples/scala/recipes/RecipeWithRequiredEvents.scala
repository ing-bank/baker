package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import examples.scala.events.{FraudCheckCompleted, PaymentReceived}
import examples.scala.interactions.ShipOrder

object RecipeWithRequiredEvents {
  val recipe: Recipe = Recipe("example")
    .withInteraction(
      ShipOrder.interaction
        .withRequiredEvent(
          FraudCheckCompleted.event
        )
        .withRequiredOneOfEvents(
          PaymentReceived.event,
          Event("UsedCouponCode")
        )
    )
}