package webshop

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

import scala.concurrent.duration._

object WebshopRecipe {

  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Events.OrderPlaced,
      Events.PaymentMade)
    .withInteractions(
      Interactions.ReserveItems
        .withRequiredEvent(Events.PaymentMade))
    .withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100 milliseconds)
        .withUntil(Some(UntilDeadline(24 hours)))
        .withMaxTimeBetweenRetries(Some(10 minutes))
        .build())

  object Ingredients {

    val OrderId: Ingredient[String] =
      Ingredient[String]("orderId")

    val Items: Ingredient[List[String]] =
      Ingredient[List[String]]("items")

    val ReservedItems: Ingredient[List[String]] =
      Ingredient[List[String]]("reservedItems")

    val UnavailableItems: Ingredient[List[String]] =
      Ingredient[List[String]]("unavailableItems")
  }

  object Events {

    val OrderPlaced: Event = Event(
      name = "OrderPlaced",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )

    val PaymentMade: Event = Event(
      name = "PaymentMade",
      providedIngredients = Seq.empty,
      maxFiringLimit = Some(1)
    )

    val OrderHadUnavailableItems: Event = Event(
      name = "OrderHadUnavailableItems",
      providedIngredients = Seq(
        Ingredients.UnavailableItems
      ),
      maxFiringLimit = Some(1)
    )

    val ItemsReserved: Event = Event(
      name = "ItemsReserved",
      providedIngredients = Seq(
        Ingredients.ReservedItems
      ),
      maxFiringLimit = Some(1)
    )
  }

  object Interactions {

    val ReserveItems: Interaction = Interaction(
      name = "ReserveItems",
      inputIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items,
      ),
      output = Seq(
        Events.OrderHadUnavailableItems,
        Events.ItemsReserved
      )
    )
  }
}
