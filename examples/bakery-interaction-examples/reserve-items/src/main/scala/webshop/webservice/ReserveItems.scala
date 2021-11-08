package webshop.webservice

import com.ing.baker.recipe.annotations.FiresEvent

import scala.concurrent.Future
import com.ing.baker.recipe.javadsl.Interaction

trait ReserveItems extends Interaction {

  case class Item(itemId: String)

  case class OrderPlaced(Items: List[Item])

  case class ReservedItems(items: List[Item], data: Array[Byte])

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[Item]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: ReservedItems) extends ReserveItemsOutput

  @FiresEvent(oneOf = Array(classOf[ItemsReserved], classOf[OrderHadUnavailableItems]))
  def apply(items: List[Item]): Future[ReserveItemsOutput]
}