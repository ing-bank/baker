package com.ing.baker.runtime.serialization


import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.serialization.EventCodecs._
import com.ing.baker.types.{ListValue, PrimitiveValue}
import io.circe.syntax._
import org.scalatest.{FunSpec, Matchers}
import scalax.collection.immutable.Graph

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

      val event2 = EventInstance("name", Map("id" -> ListValue(List(PrimitiveValue(125.toByte)))))
      event2.asJson.noSpaces shouldEqual """{"name":"name","providedIngredients":{"id":["125"]}}"""

      case class ShippingOrder(items: List[String], data: Array[Byte])

      val event3 = EventInstance.unsafeFrom(ShippingOrder(List.empty, Array(1.toByte, 5.toByte)))
      println(event3.asJson.noSpaces)

      event3.asJson.noSpaces shouldEqual """{"name":"ShippingOrder$1","providedIngredients":{"items":[],"data":["1","5"]}}"""
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

    it("should encode CompiledRecipe") {
      val recipe = CompiledRecipe("name", "recipeId", new PetriNet(Graph.empty), Marking.empty, Seq("first", "second"), Option.empty, Option.empty)
      recipe.asJson.noSpaces shouldEqual """{"name":"name","recipeId":"recipeId","validationErrors":["first","second"]}"""
    }
  }
}