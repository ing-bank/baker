package com.ing.baker.il.failurestrategy

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.ContinueAsFunctionalEvent

case class FireFunctionalEventAfterFailure(event: EventDescriptor) extends InteractionFailureStrategy {

  override def apply(n: Int): ExceptionStrategyOutcome = ContinueAsFunctionalEvent(event.name)
}
