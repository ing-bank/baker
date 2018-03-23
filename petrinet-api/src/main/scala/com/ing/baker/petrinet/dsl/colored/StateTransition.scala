package com.ing.baker.petrinet.dsl.colored

import cats.effect.IO
import com.ing.baker.petrinet.runtime._

case class StateTransition[S, E](override val id: Long,
    override val label: String,
    override val isAutomated: Boolean,
    override val exceptionStrategy: TransitionExceptionHandler[Place],
    produceEvent: S ⇒ IO[E]) extends Transition[Unit, E] {
}
