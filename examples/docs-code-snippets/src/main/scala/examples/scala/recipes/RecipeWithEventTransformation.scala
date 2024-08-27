package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe
import examples.scala.events.PaymentReceived
import examples.scala.interactions.ShipOrder

object RecipeWithEventTransformation {
  val recipe: Recipe = Recipe("example")
    .withInteraction(
      ShipOrder.interaction
        .withEventOutputTransformer(
          event = PaymentReceived.event,
          newEventName = "OrderCreated",
          ingredientRenames = Map.apply(
            ("customerId", "userId"),
            ("productIds", "skus")
          )
        )
    )
}