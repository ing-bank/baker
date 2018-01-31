package com.ing.baker.recipe.common

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
        .withDeadline(deadline)
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaximumRetries(15)
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
        .withDeadline(deadline)
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaximumRetries(4)
        .build()

      actual shouldEqual expected
    }

    "derive the correct parameters when deadline is specified and max time between retries set" in {

      val deadline = 22 seconds
      val initialDelay = 1 seconds
      val backoffFactor: Double = 2.0
      val MaxDurationBetweenRetries = 4 seconds

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaxTimeBetweenRetries(MaxDurationBetweenRetries)
        .withDeadline(deadline)
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaxTimeBetweenRetries(MaxDurationBetweenRetries)
        .withMaximumRetries(6)
        .build()

      actual shouldEqual expected
    }

    "verify that deadline is greater than initial delay" in {

      val deadline = 1 seconds
      val initialDelay = 2 seconds

      intercept[IllegalArgumentException] {
        RetryWithIncrementalBackoff.builder()
          .withInitialDelay(initialDelay)
          .withDeadline(deadline)
          .build()
      }
    }

    "retry at least once before deadline is due" in {

      val deadline = 3 seconds
      val initialDelay = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withDeadline(deadline)
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaximumRetries(1)
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
        .withDeadline(deadline)
        .build()
      val expected = RetryWithIncrementalBackoff.builder()
        .withInitialDelay(initialDelay)
        .withBackoffFactor(backoffFactor)
        .withMaximumRetries(3)
        .build()

      actual shouldEqual expected
    }
  }
}
