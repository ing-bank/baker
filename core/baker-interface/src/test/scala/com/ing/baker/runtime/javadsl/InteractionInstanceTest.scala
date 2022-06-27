package com.ing.baker.runtime.javadsl

import com.ing.baker.types.CharArray
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers

import java.util
import java.util.Optional
import scala.annotation.nowarn
import scala.collection.JavaConverters._

@nowarn
class InteractionInstanceTest extends AnyFunSpec with Matchers {
  describe("unsafeFrom") {
    describe("should create an interaction from a class with an apply method") {
      it("normally") {
        val instance = InteractionInstance.from(new SimpleInteraction)
        instance.name shouldEqual "SimpleInteraction"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.empty(), CharArray))
        instance.output shouldEqual Optional.empty()
      }

      it("and use name parameter") {
        val instance = InteractionInstance.from(new NamedInteraction)
        instance.name shouldEqual "InteractionNameVariable"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.empty(), CharArray))
        instance.output shouldEqual Optional.empty()
      }

      it("and use name of parent") {
        val instance = InteractionInstance.from(new NamedInteraction2)
        instance.name shouldEqual "ParentInteractionWithoutName"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.empty(), CharArray))
        instance.output shouldEqual Optional.empty()
      }

      it("and use name parameter of parent") {
        val instance = InteractionInstance.from(new NamedInteraction3)
        instance.name shouldEqual "ParentInteractionWithNameVariable"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.empty(), CharArray))
        instance.output shouldEqual Optional.empty()
      }

      it("and use annotations") {
        val instance = InteractionInstance.from(new AnnotatedInteraction)
        instance.name shouldEqual "AnnotatedInteraction"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.of("renamedInput"), CharArray))
        instance.output shouldEqual Optional.of(Map("SimpleEvent" -> Map("output" -> CharArray).asJava).asJava)
      }

      it("and use annotations of parent") {
        val instance = InteractionInstance.from(new AnnotatedInteraction2)
        instance.name shouldEqual "AnnotatedParentInteraction"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.of("renamedInput"), CharArray))
        instance.output shouldEqual Optional.of(Map("SimpleEvent" -> Map("output" -> CharArray).asJava).asJava)
      }

      it("and use own annotations before parents") {
        val instance = InteractionInstance.from(new AnnotatedInteraction3)
        instance.name shouldEqual "AnnotatedParentInteraction"
        instance.input shouldEqual util.Arrays.asList(InteractionInstanceInput(Optional.of("renamedInput2"), CharArray))
        instance.output shouldEqual Optional.of(Map("SimpleEvent" -> Map("output" -> CharArray).asJava).asJava)
      }
    }
    describe("should fail") {
      it("if the class does not have a apply method") {
        assertThrows[java.lang.IllegalArgumentException] {
          InteractionInstance.from(new NoApplyMethod())
        }
      }

      it("if the class has multiple apply methods") {
        assertThrows[java.lang.IllegalArgumentException] {
          InteractionInstance.from(new MultipleApplyMethods())
        }
      }
    }
  }
}
