package webshop.webservice

import scala.concurrent.Future
import com.ing.baker.recipe.javadsl.Interaction

trait ReserveItems extends Interaction {

  case class OrderId(orderId: String)

  case class Item(itemId: String)

  case class OrderPlaced(orderId: OrderId, items: List[Item])

  case class ReservedItems(items: List[Item], data: Array[Byte])

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[Item]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: ReservedItems) extends ReserveItemsOutput

  def apply(orderId: OrderId, items: List[Item]): Future[ReserveItemsOutput]
}