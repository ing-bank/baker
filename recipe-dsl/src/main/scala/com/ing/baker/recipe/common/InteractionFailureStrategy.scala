package com.ing.baker.recipe.common

import scala.annotation.tailrec
import scala.concurrent.duration.Duration

object InteractionFailureStrategy {

  case class RetryWithIncrementalBackoff(initialTimeout: Duration,
                                         backoffFactor: Double,
                                         maximumRetries: Int,
                                         maxTimeBetweenRetries: Option[Duration] = None)
    extends InteractionFailureStrategy {
    require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
    require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")
  }

  @tailrec
  private def determineHowManyTimesUntilMaxTimeIsMet(lastDelay: Duration,
                                                     backoffFactor: Double,
                                                     maxTimeBetweenRetries: Option[Duration],
                                                     deadline: Duration,
                                                     durationCounter: Duration,
                                                     timesCounter: Int): Int = {
    val nextDelay = determineNextDelay(lastDelay, backoffFactor, maxTimeBetweenRetries)
    if ((durationCounter + nextDelay) > deadline) timesCounter
    else determineHowManyTimesUntilMaxTimeIsMet(nextDelay, backoffFactor, maxTimeBetweenRetries, deadline, durationCounter + nextDelay, timesCounter + 1)
  }

  private def determineNextDelay(lastDelay: Duration,
                                 backoffFactor: Double,
                                 maxTimeBetweenRetries: Option[Duration]): Duration = {
    if (maxTimeBetweenRetries.isDefined && maxTimeBetweenRetries.get < (lastDelay * backoffFactor)) maxTimeBetweenRetries.get
    else lastDelay * backoffFactor
  }

  object RetryWithIncrementalBackoff {
    def apply(initialDelay: Duration,
              deadline: Duration,
              maxTimeBetweenRetries: Option[Duration]): RetryWithIncrementalBackoff = {
      require(deadline > initialDelay, "deadline should be greater then initialDelay")

      val backoffFactor: Double = 2.0
      val maximumRetries = determineHowManyTimesUntilMaxTimeIsMet(
        initialDelay,
        backoffFactor,
        maxTimeBetweenRetries,
        deadline,
        initialDelay,
        1)

      new RetryWithIncrementalBackoff(initialDelay, backoffFactor, maximumRetries, maxTimeBetweenRetries)
    }
  }

  case class BlockInteraction() extends InteractionFailureStrategy

}

sealed trait InteractionFailureStrategy
