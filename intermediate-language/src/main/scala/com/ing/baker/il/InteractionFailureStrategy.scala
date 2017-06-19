package com.ing.baker.il

import io.kagera.runtime.ExceptionStrategy.{BlockTransition, RetryWithDelay}
import io.kagera.runtime.TransitionExceptionHandler

import scala.concurrent.duration.{Duration, FiniteDuration}

object InteractionFailureStrategy {

  def retryWithIncrementalBackoff(initialTimeout: Duration,
                                  backoffFactor: Double = 2.0,
                                  maximumRetries: Int = 50): TransitionExceptionHandler = {
    case (e: Error, _) => BlockTransition
    case (e, n) if n < maximumRetries =>
      RetryWithDelay((initialTimeout * (Math.pow(backoffFactor, (n - 1)))).toMillis)
    case (e, n) => BlockTransition
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

  case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                         backoffFactor: Double = 2.0,
                                         maximumRetries: Int = 50)
      extends InteractionFailureStrategy {
    require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
    require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")
  }

  case object BlockInteraction extends InteractionFailureStrategy

  def asTransitionExceptionHandler(s: InteractionFailureStrategy): TransitionExceptionHandler =
    s match {
      case RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries) =>
        retryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries)
      case BlockInteraction =>
        (e, n) =>
          BlockTransition
    }
}

sealed trait InteractionFailureStrategy
