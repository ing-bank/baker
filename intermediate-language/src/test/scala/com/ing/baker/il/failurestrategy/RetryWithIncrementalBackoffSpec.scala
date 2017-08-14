package com.ing.baker.il.failurestrategy

import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome.{BlockTransition, RetryWithDelay}
import org.scalatest.{Matchers, WordSpecLike}

import scala.concurrent.duration._

class RetryWithIncrementalBackoffSpec extends WordSpecLike with Matchers {

  "The RetryWithIncrementalBackoff" should {
    "return RetryWithDelay with the correct time until the next retry" in {
      val retry = RetryWithIncrementalBackoff(Duration(1, MILLISECONDS), 2.0, 5, None, None)
      retry(1) shouldBe RetryWithDelay(1)
      retry(2) shouldBe RetryWithDelay(2)
      retry(3) shouldBe RetryWithDelay(4)
      retry(4) shouldBe RetryWithDelay(8)
    }

    "return BlockTransition when retry max times fired is met" in {
      val retry = RetryWithIncrementalBackoff(Duration(1, MILLISECONDS), 2.0, 5, None, None)
      retry(5) shouldBe BlockTransition
      retry(6) shouldBe BlockTransition
    }

    "return the max retry time when retry max time is met" in {
      val retry = RetryWithIncrementalBackoff(Duration(1, MILLISECONDS), 2.0, 10, Some(Duration(10, MILLISECONDS)), None)
      retry(4) shouldBe RetryWithDelay(8)
      retry(5) shouldBe RetryWithDelay(10)
      retry(6) shouldBe RetryWithDelay(10)
    }
  }

}
