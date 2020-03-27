package com.ing.baker.runtime.model

import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api.Marking


sealed trait FailureStrategy

object FailureStrategy {

  case object BlockTransition extends FailureStrategy

  case class RetryWithDelay(delay: Long) extends FailureStrategy {
    require(delay >= 0, "Delay must be greater then zero")
  }

  case class Continue[O](marking: Marking[Place], output: O) extends FailureStrategy
}
