package com.ing.baker.petrinet.dsl.colored

import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler

/**
 * A transition in a Colored Petri Net
 *
 * @tparam Input  The input type of the transition, the type of value that is required as input
 * @tparam Output The output type of the transition, the type of value that this transition 'emits' or 'produces'
 */
trait Transition[Input, Output] {
  val id: Long
  def label: String
  def isAutomated: Boolean
  def exceptionStrategy: TransitionExceptionHandler[Place] = (e, n, _) ⇒ BlockTransition
}