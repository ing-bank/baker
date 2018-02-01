package com.ing.baker.recipe.common

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.{UntilDeadline, UntilMaximumRetries}
import com.ing.baker.recipe.common.InteractionFailureStrategy._
import org.scalatest.{Matchers, WordSpecLike}

import scala.concurrent.duration._
import scala.language.postfixOps

class InteractionFailureStrategySpec extends WordSpecLike with Matchers {

  "RetryWithIncrementalBackoff " should {

    "derive the correct parameters when deadline is specified" in {

      val deadline = 24 hours
      val initialDelay = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilDeadline(deadline)))
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilMaximumRetries(15)))
        .build()

      actual shouldEqual expected
    }

    "derive the correct parameters when deadline is specified2" in {

      val deadline = 16 seconds
      val initialDelay = 1 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilDeadline(deadline)))
        .build()

      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilMaximumRetries(4)))
        .build()

      actual shouldEqual expected
    }

    "derive the correct parameters when deadline is specified and max time between retries set" in {

      val deadline = 22 seconds
      val initialDelay = 1 seconds
      val backoffFactor: Double = 2.0
      val maxDurationBetweenRetries = 4 seconds

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaxTimeBetweenRetries(Some(maxDurationBetweenRetries))
        .withUntil(Some(UntilDeadline(deadline)))
        .build()

      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaxTimeBetweenRetries(Some(maxDurationBetweenRetries))
        .withUntil(Some(UntilMaximumRetries(6)))
        .build()

      actual shouldEqual expected
    }

    "verify that deadline is greater than initial delay" in {

      val deadline = 1 seconds
      val initialDelay = 2 seconds

      intercept[IllegalArgumentException] {
        RetryWithIncrementalBackoff.builder()
          .withInitialDelay(initialDelay)
          .withUntil(Some(UntilDeadline(deadline)))
          .build()
      }
    }

    "retry at least once before deadline is due" in {

      val deadline = 3 seconds
      val initialDelay = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withUntil(Some(UntilDeadline(deadline)))
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilMaximumRetries(1)))
        .build()

      actual shouldEqual expected
    }

    "retry 3 times before deadline is due" in {

      val deadline = 15 seconds
      val initialDelay = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilDeadline(deadline)))
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withUntil(Some(UntilMaximumRetries(3)))
        .build()

      actual shouldEqual expected
    }
  }
}
