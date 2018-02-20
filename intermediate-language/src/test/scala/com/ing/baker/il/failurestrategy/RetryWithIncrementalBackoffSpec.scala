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
      retry(6) shouldBe BlockTransition
      retry(7) shouldBe BlockTransition
    }

    "Not fail if retry gets to big" in {
      val retry = RetryWithIncrementalBackoff(Duration(10, MILLISECONDS), 2.0, 100, Some(Duration(10, MILLISECONDS)), None)
      retry(42) shouldBe RetryWithDelay(10)
      retry(101) shouldBe BlockTransition
    }
  }
}