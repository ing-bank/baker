package com.ing.baker.il.failurestrategy

import com.ing.baker.il.EventType
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.Continue

case class FireEventAfterFailure(event: EventType) extends InteractionFailureStrategy {

  override def apply(n: Int): ExceptionStrategyOutcome = Continue(event)
}
