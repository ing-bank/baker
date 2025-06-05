package com.ing.baker.il.failurestrategy

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.{BlockTransition, Continue, ContinueAsFunctionalEvent, RetryWithDelay}
import com.ing.baker.il.failurestrategy.RetryWithIncrementalBackoff._

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.Duration

object RetryWithIncrementalBackoff {
  val oneWeekInMillis: Long = Duration.apply(7 , TimeUnit.DAYS).toMillis
}

case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                       backoffFactor: Double,
                                       maximumRetries: Int,
                                       maxTimeBetweenRetries: Option[Duration],
                                       retryExhaustedEvent: Option[EventDescriptor],
                                       retryWithFunctionalEvent: Option[EventDescriptor])
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
    else if (retryWithFunctionalEvent.isDefined) ContinueAsFunctionalEvent(retryWithFunctionalEvent.get.name)
    else BlockTransition
  }

  // Used in CompiledRecipe to generate the hash. This is a workaround to keep the hash the same.
  // This method mimics the result of toString before the retryWithFunctionalEvent was added
  override def toString: String = {
    if(retryWithFunctionalEvent.isDefined) {
      s"RetryWithIncrementalBackoff($initialTimeout,$backoffFactor,$maximumRetries,$maxTimeBetweenRetries,$retryExhaustedEvent,$retryWithFunctionalEvent)"
    } else {
      s"RetryWithIncrementalBackoff($initialTimeout,$backoffFactor,$maximumRetries,$maxTimeBetweenRetries,$retryExhaustedEvent)"
    }
  }
}