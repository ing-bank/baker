package com.ing.baker.recipe.common

import scala.annotation.tailrec
import scala.concurrent.duration.{Duration, _}

sealed trait InteractionFailureStrategy

object InteractionFailureStrategy {

  case class BlockInteraction() extends InteractionFailureStrategy

  /**
   * @deprecated
   * Please use FireEventAndBlock or FireEventAndResolve, the FireEventAndBlock is exactly as the old FireEvent
   */
  @Deprecated()
  case class FireEventAfterFailure(eventName: Option[String] = None) extends InteractionFailureStrategy

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is blocked.
   * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
   * @return
   */
  case class FireEventAndBlock(eventName: Option[String] = None) extends InteractionFailureStrategy

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
   * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
   * @return
   */
  case class FireEventAndResolve(eventName: Option[String] = None) extends InteractionFailureStrategy

  case class RetryWithIncrementalBackoff private(initialDelay: Duration,
                                                 backoffFactor: Double = 2,
                                                 maximumRetries: Int,
                                                 maxTimeBetweenRetries: Option[Duration] = None,
                                                 fireRetryExhaustedEvent: Option[Option[String]] = None,
                                                 fireFunctionalEvent: Option[Option[String]] = None) extends InteractionFailureStrategy {
    require(backoffFactor >= 1.0, "backoff factor must be greater or equal to 1.0")
    require(maximumRetries >= 1, "maximum retries must be greater or equal to 1")
  }

  object RetryWithIncrementalBackoff {

    sealed trait Until

    case class UntilDeadline(duration: Duration) extends Until

    case class UntilMaximumRetries(count: Int) extends Until

    object builder {
      def apply() = new builder()
    }

    case class builder private(
                                private val initialDelay: Duration = 1 second,
                                private val backoffFactor: Double = 2,
                                private val until: Option[Until] = None,
                                private val maxTimeBetweenRetries: Option[Duration] = None,
                                private val fireRetryExhaustedEvent: Option[Option[String]] = None,
                                private val fireFunctionalEvent: Option[Option[String]] = None) {

      def withInitialDelay(initialDelay: Duration) = this.copy(initialDelay = initialDelay)

      def withBackoffFactor(backoffFactor: Double) = this.copy(backoffFactor = backoffFactor)

      def withUntil(until: Option[Until]) = this.copy(until = until)

      def withMaxTimeBetweenRetries(maxTimeBetweenRetries: Option[Duration]) = this.copy(maxTimeBetweenRetries = maxTimeBetweenRetries)

      /**
       * @deprecated
       * Please use withFireEventAndBlock or withFireEventAndResolve, the withFireEventAndBlock is exactly as the old withFireRetryExhaustedEvent
       */
      @Deprecated()
      def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Option[String]) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent))

      /**
       * @deprecated
       * Please use withFireEventAndBlock or withFireEventAndResolve, the withFireEventAndBlock is exactly as the old withFireRetryExhaustedEvent
       */
      @Deprecated()
      def withFireRetryExhaustedEvent() = this.copy(fireRetryExhaustedEvent = Some(None))

      /**
       * @deprecated
       * Please use withFireEventAndBlock or withFireEventAndResolve, the withFireEventAndBlock is exactly as the old withFireRetryExhaustedEvent
       */
      @Deprecated()
      def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Event) = this.copy(fireRetryExhaustedEvent = Some(Some(fireRetryExhaustedEvent.name)))


      /**
       * After the interaction fails with an exception an event is thrown and the interaction is blocked.
       * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
       * @return
       */
      def withFireEventAndBlock(fireRetryExhaustedEvent: Option[String]) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent))

      /**
       * After the interaction fails with an exception an event is thrown and the interaction is blocked.
       * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
       * @return
       */
      def withFireEventAndBlock() = this.copy(fireRetryExhaustedEvent = Some(None))

      /**
       * After the interaction fails with an exception an event is thrown and the interaction is blocked.
       * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
       * @return
       */
      def withFireEventAndBlock(fireRetryExhaustedEvent: Event) = this.copy(fireRetryExhaustedEvent = Some(Some(fireRetryExhaustedEvent.name)))

      /**
       * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
       * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
       * @return
       */
      def withFireEventAndResolve(fireRetryExhaustedEvent: Option[String]) = this.copy(fireFunctionalEvent = Some(fireRetryExhaustedEvent))

      /**
       * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
       * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
       * @return
       */
      def withFireEventAndResolve() = this.copy(fireFunctionalEvent = Some(None))

      /**
       * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
       * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
       * @return
       */
      def withFireEventAndResolve(fireRetryExhaustedEvent: Event) = this.copy(fireFunctionalEvent = Some(Some(fireRetryExhaustedEvent.name)))

      def build(): RetryWithIncrementalBackoff = {
        until match {
          case Some(UntilDeadline(duration)) =>
            require(duration > initialDelay, "deadline should be greater then initialDelay")

            new RetryWithIncrementalBackoff(
              initialDelay = initialDelay,
              backoffFactor,
              maximumRetries = calculateMaxRetries(
                lastDelay = initialDelay,
                backoffFactor,
                deadline = duration,
                totalDelay = initialDelay,
                timesCounter = 1),
              maxTimeBetweenRetries,
              fireRetryExhaustedEvent,
              fireFunctionalEvent)

          case Some(UntilMaximumRetries(count)) =>
            new RetryWithIncrementalBackoff(
              initialDelay,
              backoffFactor,
              maximumRetries = count,
              maxTimeBetweenRetries,
              fireRetryExhaustedEvent,
              fireFunctionalEvent)
          case None => throw new IllegalArgumentException("Either deadline of maximum retries need to be set")
        }

      }

      @tailrec private def calculateMaxRetries(lastDelay: Duration,
                                               backoffFactor: Double,
                                               deadline: Duration,
                                               totalDelay: Duration,
                                               timesCounter: Int): Int = {

        val newDelay = lastDelay * backoffFactor
        val nextDelay = maxTimeBetweenRetries.getOrElse(newDelay).min(newDelay) // get the minimum of two

        if ((totalDelay + nextDelay) > deadline) timesCounter
        else calculateMaxRetries(nextDelay, backoffFactor, deadline, totalDelay + nextDelay, timesCounter + 1)
      }

    }

  }

}

