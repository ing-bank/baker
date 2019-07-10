package webshop

import com.ing.baker.recipe.scaladsl.{Event, Interaction, Recipe}

import scala.concurrent.Future

object WebshopRecipeReflection {

  case class OrderPlaced(orderId: String, items: List[String])

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

  trait ReserveItems {

    def apply(recipeInstanceId: String, orderId: String, items: List[String]): Future[ReserveItemsOutput]
  }

  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
    .withInteractions(
      Interaction[ReserveItems]
    )
}

