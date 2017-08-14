package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, RetryWithIncrementalBackoff}

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
      None)
  }

  def RetryWithIncrementalBackoff(initialDelay: java.time.Duration,
                                  deadline: java.time.Duration): RetryWithIncrementalBackoff = {
    val initialDelayDuration = Duration(initialDelay.toMillis, duration.MILLISECONDS)
    val deadlineDuration = Duration(deadline.toMillis, duration.MILLISECONDS)
    common.InteractionFailureStrategy.RetryWithIncrementalBackoff(
      initialDelayDuration,
      deadlineDuration,
      None,
      None)
  }

  def RetryWithIncrementalBackoff(initialDelay: java.time.Duration,
                                  deadline: java.time.Duration,
                                  maxTimeBetweenRetries: java.time.Duration,
                                  exhaustedEvent: Class[_]): RetryWithIncrementalBackoff = {
    val initialDelayDuration = Duration(initialDelay.toMillis, duration.MILLISECONDS)
    val deadlineDuration = Duration(deadline.toMillis, duration.MILLISECONDS)
    common.InteractionFailureStrategy.RetryWithIncrementalBackoff(
      initialDelayDuration,
      deadlineDuration,
      Some(Duration(maxTimeBetweenRetries.toMillis, duration.MILLISECONDS)),
      Some(eventClassToCommonEvent(exhaustedEvent, None)))
  }

  def RetryWithIncrementalBackoff(initialDelay: java.time.Duration,
                                  deadline: java.time.Duration,
                                  exhaustedEvent: Class[_]): RetryWithIncrementalBackoff = {
    val initialDelayDuration = Duration(initialDelay.toMillis, duration.MILLISECONDS)
    val deadlineDuration = Duration(deadline.toMillis, duration.MILLISECONDS)
    common.InteractionFailureStrategy.RetryWithIncrementalBackoff(
      initialDelayDuration,
      deadlineDuration,
      None,
      Some(eventClassToCommonEvent(exhaustedEvent, None)))
  }

  def BlockInteraction(): BlockInteraction = common.InteractionFailureStrategy.BlockInteraction()
}
