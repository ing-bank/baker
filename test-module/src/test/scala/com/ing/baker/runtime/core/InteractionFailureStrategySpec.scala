package com.ing.baker.runtime.core

import com.ing.baker.TestRecipeHelper
import com.ing.baker.recipe.common.InteractionFailureStrategy._

import scala.concurrent.duration._
import scala.language.postfixOps

class InteractionFailureStrategySpec extends TestRecipeHelper {

  "RetryWithIncrementalBackoff " should {

    "derive the correct paramaters when deadline is specified" in {

      val deadline              = 24 hours
      val initialDelay          = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
                                                 backoffFactor,
                                                 maximumRetries = 15)

      actual shouldEqual expected
    }

    "verify that deadline is greater than initial delay" in {

      val deadline     = 1 seconds
      val initialDelay = 2 seconds

      intercept[IllegalArgumentException] {
        RetryWithIncrementalBackoff(initialDelay, deadline)
      }
    }

    "retry at least once before deadline is due" in {

      val deadline              = 3 seconds
      val initialDelay          = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
                                                 backoffFactor,
                                                 maximumRetries = 1)

      actual shouldEqual expected
    }

    "retry 3 times before deadline is due" in {

      val deadline              = 15 seconds
      val initialDelay          = 2 seconds
      val backoffFactor: Double = 2.0

      val actual = RetryWithIncrementalBackoff(initialDelay, deadline)
      val expected = RetryWithIncrementalBackoff(initialTimeout = initialDelay,
                                                 backoffFactor,
                                                 maximumRetries = 3)

      actual shouldEqual expected
    }
  }
}
