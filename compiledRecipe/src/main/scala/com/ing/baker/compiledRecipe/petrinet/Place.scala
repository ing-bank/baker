package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.compiledRecipe.petrinet.Place.PlaceType


object Place {

  sealed trait PlaceType

  case object IngredientPlace extends PlaceType
  case object InteractionEventOutputPlace extends PlaceType
  case object FiringLimiterPlace extends PlaceType
  case object EventPreconditionPlace extends PlaceType
  case object EventOrPreconditionPlace extends PlaceType
  case object IntermediatePlace extends PlaceType
  case object EmptyEventIngredientPlace extends PlaceType
  case object MultiTransitionPlace extends PlaceType
}

case class Place[C](id: Long, label: String, placeType: PlaceType)
