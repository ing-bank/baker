package com.ing.baker.runtime.model

import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.scaladsl.EventInstance

case class TransitionFiring(id: Long,
                            transition: Transition,
                            consume: Marking[Place],
                            input: EventInstance,
                            state: TransitionState = TransitionState.ActiveTransition) {

  def isActive: Boolean = state match {
    case TransitionState.FailedTransition(_, _, _, FailureStrategy.RetryWithDelay(_)) ⇒ true
    case TransitionState.ActiveTransition ⇒ true
    case _ ⇒ false
  }

  def isFailed: Boolean = state match {
    case _: TransitionState.FailedTransition => true
    case _ => false
  }

  def failureCount: Int = state match {
    case e: TransitionState.FailedTransition ⇒ e.failureCount
    case _ => 0
  }
}
