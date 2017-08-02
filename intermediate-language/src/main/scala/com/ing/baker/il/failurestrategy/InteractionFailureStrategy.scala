package com.ing.baker.il.failurestrategy

import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler

object InteractionFailureStrategy {
  case object BlockInteraction extends InteractionFailureStrategy {
    override def asTransitionExceptionHandler(): TransitionExceptionHandler = (e, n) => BlockTransition
  }
}

trait InteractionFailureStrategy {
  def asTransitionExceptionHandler() : TransitionExceptionHandler
}
