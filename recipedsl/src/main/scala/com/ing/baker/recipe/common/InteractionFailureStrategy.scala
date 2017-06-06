package com.ing.baker.recipe.common

import scala.concurrent.duration.{Duration, FiniteDuration}

object InteractionFailureStrategy {

  case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                         backoffFactor: Double = 2.0,
                                         maximumRetries: Int = 50)
      extends InteractionFailureStrategy {
    require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
    require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")
  }

  object RetryWithIncrementalBackoff {
    def apply(initialDelay: FiniteDuration,
              deadline: FiniteDuration): RetryWithIncrementalBackoff = {
      require(deadline > initialDelay, "deadline should be greater then initialDelay")

      val backoffFactor: Double = 2.0
      val maximumRetries =
        (Math.log(deadline / initialDelay) / Math.log(backoffFactor)).round.toInt

      RetryWithIncrementalBackoff(initialDelay, backoffFactor, maximumRetries)
    }
  }
  case object BlockInteraction extends InteractionFailureStrategy
}

sealed trait InteractionFailureStrategy
