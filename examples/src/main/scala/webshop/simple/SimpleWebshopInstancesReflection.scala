package webshop.simple

import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

object SimpleWebshopInstancesReflection {

  trait ReserveItems {

    def apply(orderId: String, items: List[String]): Future[SimpleWebshopRecipeReflection.ReserveItemsOutput]
  }

  class ReserveItemsInstance extends ReserveItems {

    override def apply(orderId: String, items: List[String]): Future[SimpleWebshopRecipeReflection.ReserveItemsOutput] = {

      // Http call to the Warehouse service
      val response: Future[Either[List[String], List[String]]] =
      // This is mocked for the sake of the example
        Future.successful(Right(items))

      // Build an event instance that Baker understands
      response.map {
        case Left(unavailableItems) =>
          SimpleWebshopRecipeReflection.OrderHadUnavailableItems(unavailableItems)
        case Right(reservedItems) =>
          SimpleWebshopRecipeReflection.ItemsReserved(reservedItems)
      }
    }
  }

  val reserveItemsInstance: InteractionInstance =
    InteractionInstance.unsafeFrom(new ReserveItemsInstance)
}
