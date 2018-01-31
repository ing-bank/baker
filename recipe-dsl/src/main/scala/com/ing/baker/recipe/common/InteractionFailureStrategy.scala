package com.ing.baker.recipe.common

import scala.annotation.tailrec
import scala.concurrent.duration.{Duration, _}

sealed trait InteractionFailureStrategy

object InteractionFailureStrategy {

  case class BlockInteraction() extends InteractionFailureStrategy

  case class FireEventAfterFailure() extends InteractionFailureStrategy

  case class RetryWithIncrementalBackoff(initialDelay: Duration,
                                         backoffFactor: Double = 2,
                                         maximumRetries: Int,
                                         maxTimeBetweenRetries: Option[Duration] = None,
                                         fireRetryExhaustedEvent: Option[String] = None) extends InteractionFailureStrategy {
    require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
    require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")
  }

  object RetryWithIncrementalBackoff {

    object builder {
      def apply() = new builder()
    }

    case class builder private(
                                private var initialDelay: Duration = 1 second,
                                private var backoffFactor: Double = 2,
                                private var deadline: Option[Duration] = None,
                                private var maximumRetries: Option[Int] = None,
                                private var maxTimeBetweenRetries: Option[Duration] = None,
                                private var fireRetryExhaustedEvent: Option[String] = None) {

      def withInitialDelay(initialDelay: Duration) = this.copy(initialDelay = initialDelay)

      def withBackoffFactor(backoffFactor: Double) = this.copy(backoffFactor = backoffFactor)

      def withMaximumRetries(maximumRetries: Int) = this.copy(maximumRetries = Some(maximumRetries))

      def withMaxTimeBetweenRetries(maxTimeBetweenRetries: Duration) = this.copy(maxTimeBetweenRetries = Some(maxTimeBetweenRetries))

      def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: String) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent))

      def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Boolean) = this.copy(fireRetryExhaustedEvent = Some(defaultEventExhaustedName))

      def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Event) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent.name))

      def withDeadline(deadline: Duration) = this.copy(deadline = Some(deadline))

      def build(): RetryWithIncrementalBackoff = {
        if (deadline.isDefined) {
          require(deadline.get > initialDelay, "deadline should be greater then initialDelay")

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
            initialDelay = initialDelay,
            backoffFactor,
            maximumRetries = calculateMaxRetries(
              lastDelay = initialDelay,
              backoffFactor,
              deadline.get,
              totalDelay = initialDelay,
              timesCounter = 1),
            maxTimeBetweenRetries,
            fireRetryExhaustedEvent)
        }
        else if (maximumRetries.isDefined) {
          new RetryWithIncrementalBackoff(
            initialDelay,
            backoffFactor,
            maximumRetries.get,
            maxTimeBetweenRetries,
            fireRetryExhaustedEvent)
        }
        else {
          throw new IllegalArgumentException("Either deadline of maximum retries need to be set")
        }
      }
    }

  }

}

