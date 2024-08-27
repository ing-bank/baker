package com.ing.baker.runtime.akka.actor.process_instance.dsl

import cats.effect.IO
import com.ing.baker.il.petrinet.{Place, Transition}

case class StateTransition[S, E](
                                  override val id: Long,
                                  override val label: String,
                                  val isAutomated: Boolean,
                                  val exceptionStrategy: TransitionExceptionHandler[Place],
                                  produceEvent: S => IO[E]) extends Transition {
}
