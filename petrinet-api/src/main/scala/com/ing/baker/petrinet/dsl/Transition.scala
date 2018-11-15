package com.ing.baker.petrinet.dsl

import com.ing.baker.petrinet.api.Identifiable
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition

object Transition {
  implicit val identifiable: Identifiable[Transition] = p => p.id
}

/**
 * A transition in a Colored Petri Net
 *
 */
trait Transition {
  val id: Long
  def label: String
  def isAutomated: Boolean
  def exceptionStrategy: TransitionExceptionHandler[Place] = (e, n, _) ⇒ BlockTransition
}