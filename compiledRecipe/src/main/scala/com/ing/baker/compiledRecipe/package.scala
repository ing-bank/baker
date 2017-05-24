package com.ing.baker

import com.ing.baker.compiledRecipe.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.compiledRecipe.petrinet.InteractionTransition
import io.kagera.dsl.colored.{Place, Transition}

package object compiledRecipe {
  val limitPrefix           = "limit:"
  val preconditionPrefix    = "precondition:"
  val orPreconditionPrefix  = "orPrecondition:"
  val interactionEvent      = "result:"
  val multiTransitionPrefix = "multi:"
  val processIdName         = "$ProcessID$"
  val missingEvent          = "missing:"
  val emptyEventIngredient     = "EEI:"

  implicit class PlaceAdditions(place: Place[_]) {
    def isIngredient: Boolean =
      !isInteractionEventOutput && !isEventPrecondition && !isFiringLimiter && !isIntermediate
    def isInteractionEventOutput: Boolean = place.label.startsWith(interactionEvent)
    def isFiringLimiter: Boolean          = place.label.startsWith(limitPrefix)
    def isEventPrecondition: Boolean      = place.label.startsWith(preconditionPrefix)
    def isOrEventPrecondition: Boolean    = place.label.startsWith(orPreconditionPrefix)
    def isIntermediate: Boolean           = place.label.startsWith(multiTransitionPrefix)
    def isEmptyEventIngredient: Boolean   = place.label.startsWith(emptyEventIngredient)
  }

  implicit class TransitionAdditions(transition: Transition[_, _, _]) {
    def isParallelizationTransition: Boolean = transition.label.startsWith(multiTransitionPrefix)

    def isInteraction: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == InteractionAction
    }

    def isSieve: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == SieveAction
    }

    def isEventMissing: Boolean =
      !transition
        .isInstanceOf[InteractionTransition[_]] && transition.label.startsWith(missingEvent)

    def isEvent: Boolean =
      !(transition.isInstanceOf[InteractionTransition[_]] || transition.label.contains(":"))
  }
}
