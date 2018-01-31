package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, RetryWithIncrementalBackoff}

import scala.concurrent.duration
import scala.concurrent.duration.Duration

object InteractionFailureStrategy {

  case class RetryWithIncrementalBackoffBuilder private(private var initialDelay: Option[java.time.Duration] = None,
                                                        private var backoffFactor: Double = 2,
                                                        private var deadline: Option[java.time.Duration] = None,
                                                        private var maximumRetries: Option[Int] = None,
                                                        private var maxTimeBetweenRetries: Option[java.time.Duration] = None,
                                                        private var fireRetryExhaustedEvent: Option[String] = None) {
    def this() = this(None, 2, None, None, None, None)

    def withInitialDelay(initialDelay: java.time.Duration) = this.copy(initialDelay = Some(initialDelay))

    def withBackoffFactor(backoffFactor: Double) = this.copy(backoffFactor = backoffFactor)

    def withMaximumRetries(maximumRetries: Int) = this.copy(maximumRetries = Some(maximumRetries))

    def withMaxTimeBetweenRetries(maxTimeBetweenRetries: java.time.Duration) = this.copy(maxTimeBetweenRetries = Some(maxTimeBetweenRetries))

    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: String) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent))

    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Boolean) = this.copy(fireRetryExhaustedEvent = Some(common.defaultEventExhaustedName))

    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Class[_]) = this.copy(fireRetryExhaustedEvent = Some(fireRetryExhaustedEvent.getSimpleName))

    def withDeadline(deadline: java.time.Duration) = this.copy(deadline = Some(deadline))

    def build(): RetryWithIncrementalBackoff = {
      require(initialDelay.isDefined, "InitialDelay must be defined")

      var builder: common.InteractionFailureStrategy.RetryWithIncrementalBackoff.builder = common.InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
      if (deadline.isDefined)
        builder = builder.withDeadline(Duration(deadline.get.toMillis, duration.MILLISECONDS))
      else if (maximumRetries.isDefined)
        builder = builder.withMaximumRetries(maximumRetries.get)
      else {
        throw new IllegalArgumentException("Either deadline of maximum retries need to be set")
      }
      if (maxTimeBetweenRetries.isDefined)
        builder = builder.withMaxTimeBetweenRetries(Duration(maxTimeBetweenRetries.get.toMillis, duration.MILLISECONDS))
      if(fireRetryExhaustedEvent.isDefined)
        builder = builder.withFireRetryExhaustedEvent(fireRetryExhaustedEvent.get)
      builder
        .withInitialDelay(Duration(initialDelay.get.toMillis, duration.MILLISECONDS))
        .withBackoffFactor(backoffFactor)
        .build()
    }
  }

  def FireEvent(): common.InteractionFailureStrategy.FireEventAfterFailure =
    common.InteractionFailureStrategy.FireEventAfterFailure()

  def BlockInteraction(): BlockInteraction =
    common.InteractionFailureStrategy.BlockInteraction()
}
