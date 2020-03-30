package com.ing.baker.runtime.serialization


import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.serialization.EventCodecs._
import com.ing.baker.types.PrimitiveValue
import io.circe.syntax._
import org.scalatest.{FunSpec, Matchers}

class EventCodecsSpec extends FunSpec with Matchers {
  describe("EventCodecs") {
    it("should encode RejectReason enum") {
      RejectReason.values().foreach(
        value =>
          value.asJson.noSpaces shouldEqual (s""""${value.toString}"""")
      )
    }

    it("should encode EventInstance") {
      val event = EventInstance("name", Map("id" -> PrimitiveValue(3)))
      event.asJson.noSpaces shouldEqual """{"name":"name","providedIngredients":{"id":"3"}}"""
    }

    it("should encode ExceptionStrategyOutcome") {
      val blockException: ExceptionStrategyOutcome = ExceptionStrategyOutcome.BlockTransition
      blockException.asJson.noSpaces shouldEqual """{"BlockTransition":{}}"""

      val retryException: ExceptionStrategyOutcome = ExceptionStrategyOutcome.RetryWithDelay(10)
      retryException.asJson.noSpaces shouldEqual """{"RetryWithDelay":{"delay":10}}"""

      val continueException: ExceptionStrategyOutcome = ExceptionStrategyOutcome.Continue("event name")
      continueException.asJson.noSpaces shouldEqual """{"Continue":{"eventName":"event name"}}"""
    }

    it("should encode Throwable") {
      val exception: Throwable = new RuntimeException("message")
      println(exception.asJson.noSpaces)
      exception.asJson.noSpaces shouldEqual """{"error":"message"}"""
    }
  }
}