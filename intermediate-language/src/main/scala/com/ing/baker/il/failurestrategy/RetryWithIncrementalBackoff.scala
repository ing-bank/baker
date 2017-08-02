package com.ing.baker.il.failurestrategy

import com.ing.baker.petrinet.runtime.ExceptionStrategy.{BlockTransition, RetryWithDelay}
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler

import scala.concurrent.duration.Duration

case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                       backoffFactor: Double,
                                       maximumRetries: Int,
                                       maxTimeBetweenRetries: Option[Duration])
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

  def determineRetry(): TransitionExceptionHandler = {
    case (e: Error, _) => BlockTransition
    case (e, n) if n < maximumRetries => RetryWithDelay(determineTimeToNextRetry(n))
    case (e, n) => BlockTransition
  }

  override def asTransitionExceptionHandler(): TransitionExceptionHandler = determineRetry()
}
