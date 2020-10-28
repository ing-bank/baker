package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.petrinet.api.{Id, Marking}
import com.ing.baker.runtime.scaladsl.EventInstance

sealed trait TransitionExecutionOutcome {
  val transitionExecutionId: Long
  val transitionId: Long
}

object TransitionExecutionOutcome {

  case class Completed(transitionExecutionId: Long,
                       transitionId: Long,
                       correlationId: Option[String],
                       timeStarted: Long,
                       timeCompleted: Long,
                       consumed: Marking[Long],
                       produced: Marking[Long],
                       output: Option[EventInstance]
                      ) extends TransitionExecutionOutcome

  case class Failed(transitionExecutionId: Long,
                    transitionId: Long,
                    correlationId: Option[String],
                    timeStarted: Long,
                    timeFailed: Long,
                    consume: Marking[Id],
                    input: Option[EventInstance],
                    failureReason: String,
                    exceptionStrategy: FailureStrategy
                   ) extends TransitionExecutionOutcome
}
