package com.ing.baker.il.petrinet

import com.ing.baker.il
import com.ing.baker.il.petrinet.Place.{FiringLimiterPlace, PlaceType}
import Place._
import com.ing.baker.petrinet.api.{Id, Identifiable}

object Place {

  sealed trait PlaceType {def labelPrepend: String = ""}

  case object IngredientPlace extends PlaceType
  case object InteractionEventOutputPlace extends PlaceType
  case class  FiringLimiterPlace(maxLimit: Int) extends PlaceType
  case object EventPreconditionPlace extends PlaceType
  case object EventOrPreconditionPlace extends PlaceType { override def labelPrepend: String = "EventOrPreconditionPlace:" }
  case object IntermediatePlace extends PlaceType  { override def labelPrepend: String = "IntermediatePlace:" }
  case object EmptyEventIngredientPlace extends PlaceType
  case object MultiTransitionPlace extends PlaceType

  implicit val identifiable: Identifiable[Place[_]] = p => Id(p.id)
}

case class Place[C](label: String, placeType: PlaceType) {

  val id: Long = il.sha256HashCode(s"$placeType:$label")

  def isIngredient: Boolean = placeType == IngredientPlace

  def isInteractionEventOutput: Boolean = placeType == InteractionEventOutputPlace

  def isFiringLimiter: Boolean = placeType.isInstanceOf[FiringLimiterPlace]

  def isEventPrecondition: Boolean = placeType == EventPreconditionPlace

  def isOrEventPrecondition: Boolean = placeType == EventOrPreconditionPlace

  def isIntermediate: Boolean = placeType == IntermediatePlace

  def isEmptyEventIngredient: Boolean = placeType == EmptyEventIngredientPlace
}
