package com.ing.baker.il.failurestrategy

case object BlockInteraction extends InteractionFailureStrategy {
  def apply(n: Int) : ExceptionStrategyOutcome = ExceptionStrategyOutcome.BlockTransition
}