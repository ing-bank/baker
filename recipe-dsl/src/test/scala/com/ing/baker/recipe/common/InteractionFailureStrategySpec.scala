package com.ing.baker.recipe.common

import com.ing.baker.recipe.common.InteractionFailureStrategy._
import org.scalatest.{Matchers, WordSpecLike}

import scala.concurrent.duration._
import scala.language.postfixOps

class InteractionFailureStrategySpec extends WordSpecLike with Matchers {

  "RetryWithIncrementalBackoff " should {

    "derive the correct parameters when deadline is specified" in {

      val deadline              = 24 hours
      val initialDelay          = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline, maxTimeBetweenRetries = None)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
                                                 backoffFactor,
                                                 maximumRetries = 15)

      actual shouldEqual expected
    }

    "derive the correct parameters when deadline is specified2" in {

      val deadline              = 16 seconds
      val initialDelay          = 1 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline, None)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
        backoffFactor,
        maximumRetries = 4)

      actual shouldEqual expected
    }

    "derive the correct parameters when deadline is specified and max time between retries set" in {

      val deadline                  = 22 seconds
      val initialDelay              = 1 seconds
      val backoffFactor: Double     = 2.0
      val MaxDurationBetweenRetries = 4 seconds

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline, Some(MaxDurationBetweenRetries))
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
        backoffFactor,
        maximumRetries = 6,
        Some(4 seconds))

      actual shouldEqual expected
    }

    "verify that deadline is greater than initial delay" in {

      val deadline     = 1 seconds
      val initialDelay = 2 seconds

      intercept[IllegalArgumentException] {
        RetryWithIncrementalBackoff(initialDelay, deadline, None)
      }
    }

    "retry at least once before deadline is due" in {

      val deadline              = 3 seconds
      val initialDelay          = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline, None)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
                                                 backoffFactor,
                                                 maximumRetries = 1)

      actual shouldEqual expected
    }

    "retry 3 times before deadline is due" in {

      val deadline              = 15 seconds
      val initialDelay          = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline, None)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
                                                 backoffFactor,
                                                 maximumRetries = 3)

      actual shouldEqual expected
    }
  }
}
