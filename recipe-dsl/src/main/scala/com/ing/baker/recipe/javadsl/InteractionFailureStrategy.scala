package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.{UntilDeadline, UntilMaximumRetries, Until}
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, RetryWithIncrementalBackoff}

import scala.concurrent.duration.{Duration, MILLISECONDS}

object InteractionFailureStrategy {

  case class RetryWithIncrementalBackoffBuilder private(private val initialDelay: Option[java.time.Duration],
                                                        private val backoffFactor: Double,
                                                        private val until: Option[Until],
                                                        private val maxTimeBetweenRetries: Option[java.time.Duration],
                                                        private val fireRetryExhaustedEvent: Option[String]) {
    // initialize with defaults
    def this() = this(initialDelay = None, backoffFactor = 2, until = None, maxTimeBetweenRetries = None, fireRetryExhaustedEvent = None)

    def withInitialDelay(initialDelay: java.time.Duration) = this.copy(initialDelay = Some(initialDelay))

    def withBackoffFactor(backoffFactor: Double) = this.copy(backoffFactor = backoffFactor)

    def withMaximumRetries(count: Int) = this.copy(until = Some(UntilMaximumRetries(count)))

    def withMaxTimeBetweenRetries(maxTimeBetweenRetries: java.time.Duration) = this.copy(maxTimeBetweenRetries = Some(maxTimeBetweenRetries))

    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: String) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent))

    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Boolean) = this.copy(fireRetryExhaustedEvent = Some(common.defaultEventExhaustedName))

    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Class[_]) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent.getSimpleName))

    def withDeadline(duration: java.time.Duration) = this.copy(until = Some(UntilDeadline(Duration(duration.toMillis, MILLISECONDS))))

    def build(): RetryWithIncrementalBackoff = {
      require(initialDelay.isDefined, "InitialDelay must be defined")

      common.InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
        .withUntil(until)
        .withMaxTimeBetweenRetries(maxTimeBetweenRetries.map(d => Duration(d.toMillis, MILLISECONDS)))
        .withFireRetryExhaustedEvent(fireRetryExhaustedEvent)
        .withInitialDelay(Duration(initialDelay.get.toMillis, MILLISECONDS))
        .withBackoffFactor(backoffFactor)
        .build()
    }
  }

  def FireEvent(): common.InteractionFailureStrategy.FireEventAfterFailure = common.InteractionFailureStrategy.FireEventAfterFailure(None)

  def FireEvent(eventClass: Class[_]): common.InteractionFailureStrategy.FireEventAfterFailure = FireEvent(eventClass.getSimpleName)

  def FireEvent(eventName: String): common.InteractionFailureStrategy.FireEventAfterFailure =
    common.InteractionFailureStrategy.FireEventAfterFailure(Some(eventName))

  def BlockInteraction(): BlockInteraction =
    common.InteractionFailureStrategy.BlockInteraction()
}
