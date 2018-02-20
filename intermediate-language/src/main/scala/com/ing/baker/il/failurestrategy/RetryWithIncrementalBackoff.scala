package com.ing.baker.il.failurestrategy

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.{BlockTransition, Continue, RetryWithDelay}

import scala.concurrent.duration.Duration

case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                       backoffFactor: Double,
                                       maximumRetries: Int,
                                       maxTimeBetweenRetries: Option[Duration],
                                       retryExhaustedEvent: Option[EventDescriptor])
  extends InteractionFailureStrategy {
  require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
  require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")

  def determineTimeToNextRetry(n: Int): Long = {
    val nextRetry = initialTimeout * Math.pow(backoffFactor, n - 1)
    maxTimeBetweenRetries match {
      case Some(duration) => if (nextRetry > duration) duration.toMillis else nextRetry.toMillis
      case None => nextRetry.toMillis
    }
  }

  def apply(n: Int): ExceptionStrategyOutcome = {
    if (n <= maximumRetries) RetryWithDelay(determineTimeToNextRetry(n))
    else if (retryExhaustedEvent.isDefined) Continue(retryExhaustedEvent.get)
    else BlockTransition
  }
}
