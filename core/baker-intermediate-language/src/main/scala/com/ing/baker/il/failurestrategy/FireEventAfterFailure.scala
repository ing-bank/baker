package com.ing.baker.il.failurestrategy

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.Continue

case class FireEventAfterFailure(event: EventDescriptor) extends InteractionFailureStrategy {

  override def apply(n: Int): ExceptionStrategyOutcome = Continue(event.name)
}
