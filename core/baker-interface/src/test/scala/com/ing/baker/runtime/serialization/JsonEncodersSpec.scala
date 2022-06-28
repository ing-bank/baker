package com.ing.baker.runtime.serialization


import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceDescriptor, InteractionInstanceInput}
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.types
import com.ing.baker.types.{ListValue, PrimitiveValue}
import io.circe.syntax._
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers
import scalax.collection.immutable.Graph

import scala.collection.immutable.Seq

class JsonEncodersSpec extends AnyFunSpec with Matchers {
  describe("EventCodecs") {
    it("should encode RejectReason enum") {
      RejectReason.values().foreach(
        value =>
          value.asJson.noSpaces shouldEqual (s""""${value.toString}"""")
      )
    }

    it("should encode EventInstance") {
      val event = EventInstance("name", Map("id" -> PrimitiveValue(3)))
      event.asJson.noSpaces shouldEqual """{"name":"name","providedIngredients":{"id":{"typ":3,"styp":"java.lang.Integer","val":"3"}}}"""

      val event2 = EventInstance("name", Map("id" -> ListValue(List(PrimitiveValue(125.toByte)))))
      event2.asJson.noSpaces shouldEqual """{"name":"name","providedIngredients":{"id":{"typ":1,"val":[{"typ":3,"styp":"java.lang.Byte","val":"125"}]}}}"""

      case class ShippingOrder(items: List[String], data: Array[Byte])

      val event3 = EventInstance.unsafeFrom(ShippingOrder(List.empty, Array(1.toByte, 5.toByte)))
      event3.asJson.noSpaces shouldEqual """{"name":"ShippingOrder$1","providedIngredients":{"items":{"typ":1,"val":[]},"data":{"typ":3,"styp":"ByteArray","val":"AQU="}}}"""

      val event4 = EventInstance.unsafeFrom(ShippingOrder(List.empty, Array()))
      event4.asJson.noSpaces shouldEqual """{"name":"ShippingOrder$1","providedIngredients":{"items":{"typ":1,"val":[]},"data":{"typ":3,"styp":"ByteArray","val":""}}}"""
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
      exception.asJson.noSpaces shouldEqual """{"error":"message"}"""
    }

    it("should encode CompiledRecipe") {
      val recipe = CompiledRecipe("name", "recipeId", new PetriNet(Graph.empty), Marking.empty, Seq("first", "second"), Option.empty, Option.empty)
      recipe.asJson.noSpaces shouldEqual """{"name":"name","recipeId":"recipeId","validationErrors":["first","second"]}"""
    }

    it("should encode types.Value") {
      val typ: types.Value = types.NullValue
      typ.asJson.noSpaces shouldEqual """{"typ":0}"""

      val typ2: types.Value = types.PrimitiveValue(Array[Byte](127, 127))
      typ2.asJson.noSpaces shouldEqual """{"typ":3,"styp":"ByteArray","val":"f38="}"""

      val typ3: types.Value = types.PrimitiveValue("SuperString")
      typ3.asJson.noSpaces shouldEqual """{"typ":3,"styp":"java.lang.String","val":"SuperString"}"""

      val typ4: types.Value = types.ListValue(List(typ2, typ3))
      typ4.asJson.noSpaces shouldEqual """{"typ":1,"val":[{"typ":3,"styp":"ByteArray","val":"f38="},{"typ":3,"styp":"java.lang.String","val":"SuperString"}]}"""

      val typ5: types.Value = types.RecordValue(Map("1" -> typ2, "2" -> typ4))
      typ5.asJson.noSpaces shouldEqual """{"typ":2,"val":{"1":{"typ":3,"styp":"ByteArray","val":"f38="},"2":{"typ":1,"val":[{"typ":3,"styp":"ByteArray","val":"f38="},{"typ":3,"styp":"java.lang.String","val":"SuperString"}]}}}"""
    }

    it("should encode InteractionInstanceDescriptor") {
      val interactionInstanceDescriptor = InteractionInstanceDescriptor("id", "name", Seq(InteractionInstanceInput(Option.empty, com.ing.baker.types.CharArray)), Option.empty)
      interactionInstanceDescriptor.asJson.noSpaces shouldEqual """{"id":"id","name":"name","input":[{"name":null,"type":{"CharArray":{}}}],"output":null}"""

      val interactionInstanceDescriptor2 = InteractionInstanceDescriptor("id", "name", Seq(InteractionInstanceInput(Option.apply("inputname"), com.ing.baker.types.CharArray)), Option.empty)
      interactionInstanceDescriptor2.asJson.noSpaces shouldEqual """{"id":"id","name":"name","input":[{"name":"inputname","type":{"CharArray":{}}}],"output":null}"""

      val interactionInstanceDescriptor3 = InteractionInstanceDescriptor("id", "name", Seq(InteractionInstanceInput(Option.apply("inputname"),
        com.ing.baker.types.CharArray)),
        Option.apply(Map("outputEventName" -> Map("OutputIngredientName"-> com.ing.baker.types.CharArray))))
      interactionInstanceDescriptor3.asJson.noSpaces shouldEqual """{"id":"id","name":"name","input":[{"name":"inputname","type":{"CharArray":{}}}],"output":{"outputEventName":{"OutputIngredientName":{"CharArray":{}}}}}"""

      val interactionInstanceDescriptor4 = InteractionInstanceDescriptor("id", "name", Seq(InteractionInstanceInput(Option.apply("inputname"),
        com.ing.baker.types.CharArray)),
        Option.apply(Map("outputEventName" -> Map("OutputIngredientName"-> com.ing.baker.types.EnumType(Set("A"))))) )
      interactionInstanceDescriptor4.asJson.noSpaces shouldEqual """{"id":"id","name":"name","input":[{"name":"inputname","type":{"CharArray":{}}}],"output":{"outputEventName":{"OutputIngredientName":{"EnumType":{"options":["A"]}}}}}"""

      val interactionInstanceDescriptor5 = InteractionInstanceDescriptor("id", "name", Seq(InteractionInstanceInput(Option.empty, com.ing.baker.types.CharArray)), Some(Map()))
      interactionInstanceDescriptor5.asJson.noSpaces shouldEqual """{"id":"id","name":"name","input":[{"name":null,"type":{"CharArray":{}}}],"output":{}}"""

    }
  }
}
