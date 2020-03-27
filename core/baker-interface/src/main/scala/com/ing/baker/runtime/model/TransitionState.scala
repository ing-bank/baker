package com.ing.baker.runtime.model

sealed trait TransitionState

object TransitionState {

  case class FailedTransition(failureTime: Long,
                              failureCount: Int,
                              failureReason: String,
                              failureStrategy: FailureStrategy
                             ) extends TransitionState

  case object ActiveTransition extends TransitionState
}
