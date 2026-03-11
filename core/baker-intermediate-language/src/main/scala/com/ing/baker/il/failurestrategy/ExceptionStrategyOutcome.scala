package com.ing.baker.il.failurestrategy

object ExceptionStrategyOutcome {

  /**
    * Indicates that this transition should not be retried but other transitions in the petri net still can.
    */
  case object BlockTransition extends ExceptionStrategyOutcome

  /**
    * Retries firing the transition after some delay.
    */
  case class RetryWithDelay(delay: Long) extends ExceptionStrategyOutcome {
    require(delay >= 0, "Delay must be greater or equal then zero")
  }

  /**
   * Fires this event after a technical failure occurs and blocks the interaction from execution.
   * The interaction can only be continued using the retryInteraction method on Baker.
   * @param eventName
   */
  case class Continue(eventName: String) extends ExceptionStrategyOutcome

  /**
   * Fires this event after a technical failure occurs and does not block the interaction.
   * The interaction cannot be retried using the retryInteraction but can be started again if preconditions are met again.
   * @param eventName
   */
  case class ContinueAsFunctionalEvent(eventName: String) extends ExceptionStrategyOutcome
}

sealed trait ExceptionStrategyOutcome