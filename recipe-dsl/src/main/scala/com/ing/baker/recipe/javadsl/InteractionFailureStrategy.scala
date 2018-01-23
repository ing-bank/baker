package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, FireEventAfterFailure, RetryWithIncrementalBackoff}

import scala.concurrent.duration
import scala.concurrent.duration.Duration

object InteractionFailureStrategy {
  def RetryWithIncrementalBackoff(initialDelay: java.time.Duration,
                                  deadline: java.time.Duration,
                                  maxTimeBetweenRetries: java.time.Duration): RetryWithIncrementalBackoff = {
    val initialDelayDuration = Duration(initialDelay.toMillis, duration.MILLISECONDS)
    val deadlineDuration = Duration(deadline.toMillis, duration.MILLISECONDS)
    common.InteractionFailureStrategy.RetryWithIncrementalBackoff(
      initialDelayDuration,
      deadlineDuration,
      Some(Duration(maxTimeBetweenRetries.toMillis, duration.MILLISECONDS)),
      false)
  }

  def RetryWithIncrementalBackoff(initialDelay: java.time.Duration,
                                  deadline: java.time.Duration): RetryWithIncrementalBackoff = {
    val initialDelayDuration = Duration(initialDelay.toMillis, duration.MILLISECONDS)
    val deadlineDuration = Duration(deadline.toMillis, duration.MILLISECONDS)
    common.InteractionFailureStrategy.RetryWithIncrementalBackoff(
      initialDelayDuration,
      deadlineDuration,
      None,
      false)
  }

  def RetryWithIncrementalBackoff(initialDelay: java.time.Duration,
                                  deadline: java.time.Duration,
                                  maxTimeBetweenRetries: java.time.Duration,
                                  fireRetryExhaustedEvent: Boolean): RetryWithIncrementalBackoff = {
    val initialDelayDuration = Duration(initialDelay.toMillis, duration.MILLISECONDS)
    val deadlineDuration = Duration(deadline.toMillis, duration.MILLISECONDS)
    common.InteractionFailureStrategy.RetryWithIncrementalBackoff(
      initialDelayDuration,
      deadlineDuration,
      Some(Duration(maxTimeBetweenRetries.toMillis, duration.MILLISECONDS)),
      fireRetryExhaustedEvent)
  }

  def FireEvent(): common.InteractionFailureStrategy.FireEventAfterFailure =
    common.InteractionFailureStrategy.FireEventAfterFailure()

  def BlockInteraction(): BlockInteraction =
    common.InteractionFailureStrategy.BlockInteraction()
}
