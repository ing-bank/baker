package examples.scala.events

import examples.scala.ingredients.Address

case class OrderPlaced(
  orderId: String,
  customerId: String,
  address: Address,
  productIds: List[String]
)
