package com.ing.baker.runtime.akka.internal

import cats.effect.{ContextShift, IO}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.runtime.scaladsl.{InteractionInstance, InteractionInstanceInput}
import com.ing.baker.types
import com.ing.baker.types.{EnumType, Int16, Int32, Type}
import org.mockito.Mockito.when
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatestplus.mockito.MockitoSugar

import scala.concurrent.ExecutionContext

class InteractionManagerSpec extends AnyWordSpecLike with Matchers with MockitoSugar {
  implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)
  "getImplementation" should {
    "return Some" when {
      "an interaction implementation is available" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "an interaction implementation is available with input subset of Enum" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty,  EnumType(Set("A")))))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName",  EnumType(Set("A", "B")))
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "an interaction implementation is available with input name" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option("ingredientName"), types.Int32)))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "an interaction implementation is available with output defined" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> Int32, "outputIngredient2" -> Int16))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", Int32), IngredientDescriptor("outputIngredient2", Int16)))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "an interaction implementation is available with output defined and a subset of the give output events" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> Int32, "outputIngredient2" -> Int16))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(
          Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", Int32), IngredientDescriptor("outputIngredient2", Int16))),
            EventDescriptor("outputEvent2", Seq(IngredientDescriptor("outputIngredient", Int32), IngredientDescriptor("outputIngredient2", Int16)))
          ))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "an interaction implementation is available with output defined and a subset of the enum" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> EnumType(Set("A", "B"))))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(
          Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", EnumType(Set("A", "B", "C")))))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "an interaction implementation is available with output defined and a superset of the enum with allowSupersetForOutputTypes true" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> EnumType(Set("A", "B", "C"))))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(
          Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", EnumType(Set("A", "B")))))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation), allowSupersetForOutputTypes = true)
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation.name
        found.input shouldBe interactionImplementation.input
        found.output shouldBe interactionImplementation.output
      }

      "multiple interaction implementations are available" in {
        val interactionImplementation1 = mock[InteractionInstance]
        when(interactionImplementation1.name).thenReturn("InteractionName")
        when(interactionImplementation1.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation1.output).thenReturn(None)

        val interactionImplementation2 = mock[InteractionInstance]
        when(interactionImplementation2.name).thenReturn("InteractionName2")
        when(interactionImplementation2.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation2.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation1, interactionImplementation2))

        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation1.name
        found.input shouldBe interactionImplementation1.input
        found.output shouldBe interactionImplementation1.output
      }

      "two implementations with the same correct name but only one has the correct input types" in {
        val interactionImplementation1 = mock[InteractionInstance]
        when(interactionImplementation1.name).thenReturn("InteractionName")
        when(interactionImplementation1.input).thenReturn(Seq.empty[InteractionInstanceInput])
        when(interactionImplementation1.output).thenReturn(None)

        val interactionImplementation2 = mock[InteractionInstance]
        when(interactionImplementation2.name).thenReturn("InteractionName")
        when(interactionImplementation2.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation2.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation1, interactionImplementation2))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation2.name
        found.input shouldBe interactionImplementation2.input
        found.output shouldBe interactionImplementation2.output
      }

      "two implementations with the same correct name but only one has the correct output" in {
        val interactionImplementation1 = mock[InteractionInstance]
        when(interactionImplementation1.name).thenReturn("InteractionName")
        when(interactionImplementation1.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation1.output).thenReturn(Some(Map("wrongOutputEvent"-> Map.empty[String, Type])))

        val interactionImplementation2 = mock[InteractionInstance]
        when(interactionImplementation2.name).thenReturn("InteractionName")
        when(interactionImplementation2.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation2.output).thenReturn(Some(Map("outputEvent"-> Map.empty[String, Type])))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq.empty)))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation1, interactionImplementation2))
        val found = interactionManager.findFor(interactionTransition).unsafeRunSync().get
        found.name shouldBe interactionImplementation2.name
        found.input shouldBe interactionImplementation2.input
        found.output shouldBe interactionImplementation2.output
      }
    }

    "return None" when {
      "an interaction implementation has a wrong name" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("WrongInteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a wrong ingredient input type" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.CharArray)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a wrong output event name" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(Some(Map("wrongOutputEvent"-> Map.empty[String, Type])))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq.empty)))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a wrong output event ingredient name" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("wrongOutputIngredient" -> Int32, "outputIngredient2" -> Int16))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", Int32), IngredientDescriptor("outputIngredient2", Int16)))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a wrong output event ingredient type" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> Int32, "outputIngredient2" -> Int16))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", Int16), IngredientDescriptor("outputIngredient2", Int16)))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a wrong output event enum" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> EnumType(Set("A", "B"))))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", EnumType(Set("A", "C")))))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a wrong output event with extra values for the enum" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(Some(Map("outputEvent"-> Map("outputIngredient" -> EnumType(Set("A", "B", "C"))))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", EnumType(Set("A", "B")))))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has a extra output event defined" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(
          Some(Map(
            "outputEvent"-> Map("outputIngredient" -> EnumType(Set("A", "B", "C"))),
            "outputEvent2"-> Map("outputIngredient" -> EnumType(Set("A", "B", "C"))))))

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))
        when(interactionTransition.originalEvents).thenReturn(Seq(EventDescriptor("outputEvent", Seq(IngredientDescriptor("outputIngredient", EnumType(Set("A", "C")))))))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has extra ingredient input types" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32),InteractionInstanceInput(Option.empty, types.CharArray)))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "an interaction implementation has not enough ingredient input types" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(InteractionInstanceInput(Option.empty, types.Int32)))
        when(interactionImplementation.output).thenReturn(None)

        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        val ingredientDescriptor2: IngredientDescriptor = IngredientDescriptor("ingredientName2", types.CharArray)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor, ingredientDescriptor2))

        val interactionManager: CachedInteractionManager = CachedInteractionManager(List(interactionImplementation))
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }

      "empty interaction seq" in {
        val interactionManager: CachedInteractionManager = CachedInteractionManager()

        val interactionTransition: InteractionTransition = mock[InteractionTransition]
        interactionManager.findFor(interactionTransition).unsafeRunSync() shouldBe None
      }
    }
  }
}
