package com.ing.baker.il.failurestrategy

import java.util.concurrent.TimeUnit

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.il.failurestrategy.RetryWithIncrementalBackoff._

import scala.concurrent.duration.Duration

object RetryWithIncrementalBackoff {
  val oneWeekInMillis: Long = Duration.apply(7 , TimeUnit.DAYS).toMillis
}

case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                       backoffFactor: Double,
                                       maximumRetries: Int,
                                       maxTimeBetweenRetries: Option[Duration],
                                       retryExhaustedEvent: Option[EventDescriptor])
  extends InteractionFailureStrategy {
  require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
  require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")

  def determineTimeToNextRetry(n: Int): Long = {
    val nextRetry: Long = initialTimeout.toMillis * Math.pow(backoffFactor, n - 1).toLong
    val positiveNextRetry: Long = if (nextRetry > oneWeekInMillis || nextRetry <= 0) oneWeekInMillis else nextRetry

    maxTimeBetweenRetries match {
      case Some(duration) => if (positiveNextRetry > duration.toMillis) duration.toMillis else positiveNextRetry
      case None => positiveNextRetry
    }
  }

  def apply(n: Int): ExceptionStrategyOutcome = {
    if (n <= maximumRetries) RetryWithDelay(determineTimeToNextRetry(n))
    else if (retryExhaustedEvent.isDefined) Continue(retryExhaustedEvent.get.name)
    else BlockTransition
  }
}