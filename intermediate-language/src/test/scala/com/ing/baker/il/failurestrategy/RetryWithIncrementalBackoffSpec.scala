package com.ing.baker.il.failurestrategy

import com.ing.baker.petrinet.runtime.ExceptionStrategy.{BlockTransition, RetryWithDelay}
import org.scalatest.{Matchers, WordSpecLike}

import scala.concurrent.duration._

class RetryWithIncrementalBackoffSpec extends WordSpecLike with Matchers {

  "The RetryWithIncrementalBackoff" should {
    "return RetryWithDelay with the correct time until the next retry" in {
      val retry = RetryWithIncrementalBackoff(Duration(1, MILLISECONDS), 2.0, 5, None)
      retry.determineRetry().apply(new Exception, 1) shouldBe RetryWithDelay(1)
      retry.determineRetry().apply(new Exception, 2) shouldBe RetryWithDelay(2)
      retry.determineRetry().apply(new Exception, 3) shouldBe RetryWithDelay(4)
      retry.determineRetry().apply(new Exception, 4) shouldBe RetryWithDelay(8)
    }

    "return BlockTransition when an error occurred" in {
      val retry = RetryWithIncrementalBackoff(Duration(10, MILLISECONDS), 2.0, 50, None)
      retry.determineRetry().apply(new Error, 1) shouldBe BlockTransition
    }

    "return BlockTransition when retry max times fired is met" in {
      val retry = RetryWithIncrementalBackoff(Duration(1, MILLISECONDS), 2.0, 5, None)
      retry.determineRetry().apply(new Exception, 5) shouldBe BlockTransition
      retry.determineRetry().apply(new Exception, 6) shouldBe BlockTransition
    }

    "return the max retry time when retry max time is met" in {
      val retry = RetryWithIncrementalBackoff(Duration(1, MILLISECONDS), 2.0, 10, Some(Duration(10, MILLISECONDS)))
      retry.determineRetry().apply(new Exception, 4) shouldBe RetryWithDelay(8)
      retry.determineRetry().apply(new Exception, 5) shouldBe RetryWithDelay(10)
      retry.determineRetry().apply(new Exception, 6) shouldBe RetryWithDelay(10)
    }
  }

}
