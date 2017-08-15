package com.ing.baker.petrinet.dsl.colored

import fs2.Task
import com.ing.baker.petrinet.runtime._

case class StateTransition[S, E](override val id: Long,
    override val label: String,
    override val isAutomated: Boolean,
    override val exceptionStrategy: TransitionExceptionHandler[Place],
    produceEvent: S ⇒ Task[E]) extends Transition[Unit, E] {
}
