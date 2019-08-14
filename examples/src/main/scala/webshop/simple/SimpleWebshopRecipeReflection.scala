package webshop.simple

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

import scala.concurrent.duration._

object SimpleWebshopRecipeReflection {

  case class OrderPlaced(orderId: String, items: List[String])

  case class PaymentMade()

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

  val ReserveItems = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
      Ingredient[String]("orderId"),
      Ingredient[List[String]]("items")
    ),
    output = Seq(
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
  )

  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[PaymentMade])
    .withInteractions(
      ReserveItems
        .withRequiredEvent(Event[PaymentMade]))
    .withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100 milliseconds)
        .withUntil(Some(UntilDeadline(24 hours)))
        .withMaxTimeBetweenRetries(Some(10 minutes))
        .build())
}

