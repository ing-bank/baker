package io.kagera.dsl.colored

import fs2.Task
import io.kagera.runtime._

case class StateTransition[S, E](override val id: Long,
    override val label: String,
    override val isAutomated: Boolean,
    override val exceptionStrategy: TransitionExceptionHandler,
    produceEvent: S ⇒ Task[E]) extends Transition[Unit, E] {
}
