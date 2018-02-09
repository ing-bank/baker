package com.ing.baker.il.failurestrategy

import com.ing.baker.il.EventDescriptor

object ExceptionStrategyOutcome {

  /**
    * Indicates that this transition should not be retried but other transitions in the petri net still can.
    */
  case object BlockTransition extends ExceptionStrategyOutcome

  /**
    * Retries firing the transition after some delay.
    */
  case class RetryWithDelay(delay: Long) extends ExceptionStrategyOutcome {
    require(delay > 0, "Delay must be greater then zero")
  }

  case class Continue(eventType: EventDescriptor) extends ExceptionStrategyOutcome {}
}

sealed trait ExceptionStrategyOutcome