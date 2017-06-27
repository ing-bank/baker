package com.ing.baker

import com.ing.baker.il.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.il.petrinet.Place._
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, MissingEventTransition, MultiFacilitatorTransition, Place, Transition}


package object il {
  val processIdName         = "$ProcessID$"

  implicit class PlaceAdditions(place: Place[_]) {
    def isIngredient: Boolean = place.placeType == IngredientPlace
    def isInteractionEventOutput: Boolean = place.placeType == InteractionEventOutputPlace
    def isFiringLimiter: Boolean          = place.placeType == FiringLimiterPlace
    def isEventPrecondition: Boolean      = place.placeType == EventPreconditionPlace
    def isOrEventPrecondition: Boolean    = place.placeType == EventOrPreconditionPlace
    def isIntermediate: Boolean           = place.placeType == IntermediatePlace
    def isEmptyEventIngredient: Boolean   = place.placeType == EmptyEventIngredientPlace
  }

  implicit class TransitionAdditions(transition: Transition[_, _]) {

    def isInteraction: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == InteractionAction
    }

    def isMultiFacilitatorTransition: Boolean = transition.isInstanceOf[MultiFacilitatorTransition]

    def isSieve: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == SieveAction
    }

    def isEventMissing: Boolean =
      transition match {
        case MissingEventTransition(_, _) => true
        case _ => false
      }

    def isEvent: Boolean =
      !(transition.isInstanceOf[InteractionTransition[_]] || transition.label.contains(":"))
  }
}
