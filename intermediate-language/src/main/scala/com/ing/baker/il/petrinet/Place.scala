package com.ing.baker.il.petrinet

import com.ing.baker.il
import com.ing.baker.il.petrinet.Place.PlaceType


object Place {

  sealed trait PlaceType {def labelPrepend: String = ""}

  case object IngredientPlace extends PlaceType
  case object InteractionEventOutputPlace extends PlaceType
  case class  FiringLimiterPlace(maxLimit: Int) extends PlaceType
  case object EventPreconditionPlace extends PlaceType
  case object EventOrPreconditionPlace extends PlaceType {override def labelPrepend: String = "EventOrPreconditionPlace:"}
  case object IntermediatePlace extends PlaceType
  case object EmptyEventIngredientPlace extends PlaceType
  case object MultiTransitionPlace extends PlaceType
}

case class Place[C](label: String, placeType: PlaceType) {
  val id: Long = il.sha256HashCode(s"$placeType:$label")
}
