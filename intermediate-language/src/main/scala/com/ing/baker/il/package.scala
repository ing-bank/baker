package com.ing.baker

import java.security.MessageDigest

import com.ing.baker.il.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.il.petrinet.Place._
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, MissingEventTransition, MultiFacilitatorTransition, Place, Transition}


package object il {

  val processIdName = "$ProcessID$"
  val SuccessEventAppend = "Successful"
  val exhaustedEventAppend = "RetryExhausted"

  implicit class PlaceAdditions(place: Place[_]) {
    def isIngredient: Boolean = place.placeType == IngredientPlace

    def isInteractionEventOutput: Boolean = place.placeType == InteractionEventOutputPlace

    def isFiringLimiter: Boolean = place.placeType.isInstanceOf[FiringLimiterPlace]

    def isEventPrecondition: Boolean = place.placeType == EventPreconditionPlace

    def isOrEventPrecondition: Boolean = place.placeType == EventOrPreconditionPlace

    def isIntermediate: Boolean = place.placeType == IntermediatePlace

    def isEmptyEventIngredient: Boolean = place.placeType == EmptyEventIngredientPlace
  }

  implicit class TransitionAdditions(transition: Transition[_]) {

    def isInteraction: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == InteractionAction
    }

    def isMultiFacilitatorTransition: Boolean = transition.isInstanceOf[MultiFacilitatorTransition]

    def isSieve: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == SieveAction
    }

    def isEventMissing: Boolean = transition.isInstanceOf[MissingEventTransition[_]]

    def isSensoryEvent: Boolean =
      transition match {
      case EventTransition(_, true, _) => true
      case _ => false
    }
  }

  def sha256HashCode(str: String): Long = {
    val sha256Digest: MessageDigest = MessageDigest.getInstance("SHA-256")
    BigInt(1, sha256Digest.digest(str.getBytes("UTF-8"))).toLong
  }
}
