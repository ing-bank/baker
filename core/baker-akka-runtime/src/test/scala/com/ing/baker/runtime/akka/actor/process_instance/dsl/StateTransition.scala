package com.ing.baker.runtime.akka.actor.process_instance.dsl

import cats.effect.IO
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}

case class StateTransition(
                                  override val id: Long,
                                  override val label: String,
                                  val isAutomated: Boolean,
                                  val exceptionStrategy: TransitionExceptionHandler[Place],
                                  produceEvent: RecipeInstanceState => IO[EventInstance]) extends Transition {
}
