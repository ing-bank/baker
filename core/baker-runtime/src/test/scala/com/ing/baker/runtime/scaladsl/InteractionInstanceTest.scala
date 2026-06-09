package com.ing.baker.runtime.scaladsl

import com.ing.baker.recipe.annotations.{FiresEvent, RequiresIngredient}
import com.ing.baker.runtime.scaladsl.InteractionInstanceTest._
import com.ing.baker.types.CharArray
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers

object InteractionInstanceTest {
  case class SimpleEvent(output: String)

  class SimpleInteraction() {
    def apply(input: String): SimpleEvent = SimpleEvent("output")
  }

  class NamedInteraction() {
    val name = "InteractionNameViaVariable"
    def apply(input: String): SimpleEvent = SimpleEvent("output")
  }

  trait ParentInteractionWithoutName {
    def apply(input: String): SimpleEvent
  }

  class NamedInteraction2() extends ParentInteractionWithoutName {
    def apply(input: String): SimpleEvent = SimpleEvent("output")
  }

  trait ParentInteractionWithName {
    val name = "ParentInteractionWithNameViaVariable"
    def apply(input: String): SimpleEvent
  }

  class NamedInteraction3() extends ParentInteractionWithName {
    def apply(input: String): SimpleEvent = SimpleEvent("output")
  }

  class AnnotatedInteraction() {
    @FiresEvent(oneOf = Array{classOf[SimpleEvent]})
    def apply(@RequiresIngredient("renamedInput") input: String): SimpleEvent = SimpleEvent("output")
  }

  trait ParentInteraction {
    @FiresEvent(oneOf = Array{classOf[SimpleEvent]})
    def apply(@RequiresIngredient("renamedInput") input: String): SimpleEvent
  }

  class AnnotatedInteraction2() extends ParentInteraction {
    def apply(input: String): SimpleEvent = SimpleEvent("output")
  }

  class AnnotatedInteraction3() extends ParentInteraction {
    def apply(@RequiresIngredient("renamedInput2") input: String): SimpleEvent = SimpleEvent("output")
  }

  class NoApplyMethod()

  class MultipleApplyMethods() {
    def apply() = {}
    def apply(input: String) = {}
  }
}


class InteractionInstanceTest extends AnyFunSpec with Matchers {
  implicit val ec: scala.concurrent.ExecutionContext = scala.concurrent.ExecutionContext.global

  describe("unsafeFrom") {
    describe("should create an interaction from a class with an apply method") {
      it("normally") {
        val instance = InteractionInstance.unsafeFrom(new SimpleInteraction)
        instance.name shouldEqual "SimpleInteraction"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option.empty, CharArray))
        instance.output shouldEqual None
      }

      it("and use name parameter") {
        val instance = InteractionInstance.unsafeFrom(new NamedInteraction)
        instance.name shouldEqual "InteractionNameViaVariable"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option.empty, CharArray))
        instance.output shouldEqual None
      }

      it("and use name of parent") {
        val instance = InteractionInstance.unsafeFrom(new NamedInteraction2)
        instance.name shouldEqual "ParentInteractionWithoutName"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option.empty, CharArray))
        instance.output shouldEqual None
      }

      it("and use name parameter of parent") {
        val instance = InteractionInstance.unsafeFrom(new NamedInteraction3)
        instance.name shouldEqual "ParentInteractionWithNameViaVariable"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option.empty, CharArray))
        instance.output shouldEqual None
      }

      it("and use annotations") {
        val instance = InteractionInstance.unsafeFrom(new AnnotatedInteraction)
        instance.name shouldEqual "AnnotatedInteraction"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option("renamedInput"), CharArray))
        instance.output shouldEqual Some(Map("SimpleEvent" -> Map("output" -> CharArray)))
      }

      it("and use annotations of parent") {
        val instance = InteractionInstance.unsafeFrom(new AnnotatedInteraction2)
        instance.name shouldEqual "ParentInteraction"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option("renamedInput"), CharArray))
        instance.output shouldEqual Some(Map("SimpleEvent" -> Map("output" -> CharArray)))
      }

      it("and use own annotations before parents") {
        val instance = InteractionInstance.unsafeFrom(new AnnotatedInteraction3)
        instance.name shouldEqual "ParentInteraction"
        instance.input shouldEqual Seq(InteractionInstanceInput(Option("renamedInput2"), CharArray))
        instance.output shouldEqual Some(Map("SimpleEvent" -> Map("output" -> CharArray)))
      }
    }
    describe("should fail") {
      it("if the class does not have a apply method") {
        assertThrows[java.lang.IllegalArgumentException] {
          InteractionInstance.unsafeFrom(new NoApplyMethod)
        }
      }

      it("if the class has multiple apply methods") {
        assertThrows[java.lang.IllegalArgumentException] {
          InteractionInstance.unsafeFrom(new MultipleApplyMethods)
        }
      }
    }
  }
}
