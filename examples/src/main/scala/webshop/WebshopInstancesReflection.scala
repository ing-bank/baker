package webshop

import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global

object WebshopInstancesReflection {

  trait ReserveItems {

    def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput]
  }

  val reserveItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(
    new ReserveItems {

      def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput] = {

        // Http call to the Warehouse service
        val response: Future[Either[List[String], List[String]]] =
        // This is mocked for the sake of the example
          Future.successful(Right(items))

        // Build an event instance that Baker understands
        response.map {
          case Left(unavailableItems) =>
            WebshopRecipeReflection.OrderHadUnavailableItems(unavailableItems)
          case Right(reservedItems) =>
            WebshopRecipeReflection.ItemsReserved(reservedItems)
        }
      }
    }
  )
}
