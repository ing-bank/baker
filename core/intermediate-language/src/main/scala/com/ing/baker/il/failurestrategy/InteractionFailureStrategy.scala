package com.ing.baker.il.failurestrategy

trait InteractionFailureStrategy {
  def apply(n: Int): ExceptionStrategyOutcome
}
