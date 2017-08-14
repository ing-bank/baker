package com.ing.baker.recipe.common

import com.ing.baker.recipe.common

import scala.annotation.tailrec
import scala.concurrent.duration.Duration

sealed trait InteractionFailureStrategy

object InteractionFailureStrategy {

  case class BlockInteraction() extends InteractionFailureStrategy

  case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                         backoffFactor: Double,
                                         maximumRetries: Int,
                                         maxTimeBetweenRetries: Option[Duration] = None,
                                         retryExhaustedEvent: Option[common.Event] = None) extends InteractionFailureStrategy {
    require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
    require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")
  }

  object RetryWithIncrementalBackoff {
    def apply(initialDelay: Duration,
              deadline: Duration,
              maxTimeBetweenRetries: Option[Duration],
              exhaustedEvent: Option[common.Event]): RetryWithIncrementalBackoff = {

      require(deadline > initialDelay, "deadline should be greater then initialDelay")

      val backoffFactor = 2.0

      @tailrec def calculateMaxRetries(lastDelay: Duration,
                                       backoffFactor: Double,
                                       deadline: Duration,
                                       totalDelay: Duration,
                                       timesCounter: Int): Int = {

        def min(d1Option: Option[Duration], d2: Duration): Duration = d1Option match {
          case Some(d) if d < d2 => d
          case _ => d2
        }

        val nextDelay = min(maxTimeBetweenRetries, lastDelay * backoffFactor)

        if ((totalDelay + nextDelay) > deadline) timesCounter
        else calculateMaxRetries(nextDelay, backoffFactor, deadline, totalDelay + nextDelay, timesCounter + 1)
      }

      new RetryWithIncrementalBackoff(
        initialTimeout = initialDelay,
        backoffFactor,
        maximumRetries = calculateMaxRetries(
          lastDelay = initialDelay,
          backoffFactor,
          deadline,
          totalDelay = initialDelay,
          timesCounter = 1),
        maxTimeBetweenRetries,
        exhaustedEvent)
    }
  }

}

