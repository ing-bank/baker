package com.ing.baker.il.failurestrategy

import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler

case object BlockInteraction extends InteractionFailureStrategy {
  override def asTransitionExceptionHandler(): TransitionExceptionHandler = (_, _) => BlockTransition
}