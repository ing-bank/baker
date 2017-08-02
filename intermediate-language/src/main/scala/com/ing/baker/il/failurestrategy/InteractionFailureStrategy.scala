package com.ing.baker.il.failurestrategy

import com.ing.baker.petrinet.runtime.TransitionExceptionHandler

trait InteractionFailureStrategy {
  def asTransitionExceptionHandler() : TransitionExceptionHandler
}
