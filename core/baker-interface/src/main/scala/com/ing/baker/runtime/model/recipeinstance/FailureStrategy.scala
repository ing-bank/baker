package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.scaladsl.EventInstance

sealed trait FailureStrategy

object FailureStrategy {

  case object BlockTransition extends FailureStrategy

  case class Continue(marking: Marking[Place], output: Option[EventInstance]) extends FailureStrategy

  case class RetryWithDelay(delay: Long) extends FailureStrategy { require(delay >= 0, "Delay must be greater then zero") }
}
