package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.runtime.scaladsl.EventInstance

sealed trait FailureStrategy

object FailureStrategy {

  case object BlockTransition extends FailureStrategy

  case class Continue(output: Option[EventInstance]) extends FailureStrategy

  case class RetryWithDelay(delay: Long) extends FailureStrategy { require(delay >= 0, "Delay must be greater then zero") }
}
