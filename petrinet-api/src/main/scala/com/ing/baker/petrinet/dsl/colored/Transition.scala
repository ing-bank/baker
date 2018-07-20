package com.ing.baker.petrinet.dsl.colored

import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition

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