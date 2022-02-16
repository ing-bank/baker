package webshop.simple

import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance, InteractionInstanceInput}
import com.ing.baker.types.{CharArray, ListType, ListValue, PrimitiveValue}

import scala.collection.immutable.Seq
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

object SimpleWebshopInstances {

  val ReserveItemsInstance: InteractionInstance = InteractionInstance(
    name = SimpleWebshopRecipe.Interactions.ReserveItems.name,
    input = Seq(InteractionInstanceInput(Option.empty, ListType(CharArray))),
    run = handleReserveItems
  )

  def handleReserveItems(input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {

    val validatedInput: Option[List[String]] =
      for {
        rawItems <- input.find(_.name == "items")
        items <- rawItems match {
          case IngredientInstance(_, ListValue(entries)) =>
            Some(entries)
          case _ =>
            None
        }
      } yield items.map(_.as[String])

    // Http call to the Warehouse service
    val response: Future[Either[List[String], List[String]]] =
      // This is mocked for the sake of the example
      Future.successful(Right(validatedInput.get))

    // Build an event instance that Baker understands
    response.map {

      case Left(unavailableItems) =>
        Some(EventInstance(
          name = SimpleWebshopRecipe.Events.OrderHadUnavailableItems.name,
          providedIngredients = Map(
            SimpleWebshopRecipe.Ingredients.UnavailableItems.name ->
              ListValue(unavailableItems.map(PrimitiveValue.apply))
          )
        ))

      case Right(reservedItems) =>
        Some(EventInstance(
          name = SimpleWebshopRecipe.Events.ItemsReserved.name,
          providedIngredients = Map(
            SimpleWebshopRecipe.Ingredients.ReservedItems.name ->
              ListValue(reservedItems.map(PrimitiveValue.apply))
          )
        ))
    }
  }
}
