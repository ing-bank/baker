package com.ing.baker.runtime.model

import com.ing.baker.petrinet.api.{Id, Marking}
import com.ing.baker.runtime.scaladsl.EventInstance

sealed trait TransitionEvent {
  val transitionFiringId: Long
  val transitionId: Long
}

object TransitionEvent {

  case class Fired(transitionFiringId: Long,
                   transitionId: Long,
                   timeStarted: Long,
                   timeCompleted: Long,
                   consumed: Marking[Long],
                   produced: Marking[Long],
                   output: EventInstance) extends TransitionEvent

  case class Failed(transitionFiringId: Long,
                    transitionId: Long,
                    correlationId: Option[String],
                    timeStarted: Long,
                    timeFailed: Long,
                    consume: Marking[Id],
                    input: Any,
                    failureReason: String,
                    exceptionStrategy: FailureStrategy) extends TransitionEvent
}
