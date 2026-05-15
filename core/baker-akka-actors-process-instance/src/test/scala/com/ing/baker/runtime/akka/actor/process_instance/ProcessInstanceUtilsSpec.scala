package com.ing.baker.runtime.akka.actor.process_instance

import akka.event.DiagnosticLoggingAdapter
import com.ing.baker.il.failurestrategy.{BlockInteraction, FireEventAfterFailure, InteractionFailureStrategy, RetryWithIncrementalBackoff}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.runtime.akka.internal.FatalInteractionException
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import com.ing.baker.types.Converters
import org.mockito.Mockito.mock
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpec

import java.time.Duration
import scala.concurrent.duration.Duration.Zero
import scala.concurrent.duration._

/**
 * Isolated unit tests for ProcessInstance utility methods.
 * 
 * These tests were extracted from ProcessInstanceSpec to test the business logic
 * of event name determination and wait time extraction in isolation, without
 * requiring full actor lifecycle, persistence, or event sourcing infrastructure.
 * 
 * Methods tested:
 * - ProcessInstance.getOutputEventName: Determines which event to fire for delayed transitions
 * - ProcessInstance.getWaitTimeInMillis: Extracts duration from ingredients
 */
class ProcessInstanceUtilsSpec extends AnyWordSpec with Matchers {

  val logMock: DiagnosticLoggingAdapter = mock(classOf[DiagnosticLoggingAdapter])

  "ProcessInstance.getOutputEventName" should {

    "correctly determine the output event name for simple delayed transitions" in {
      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy = BlockInteraction

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      output shouldBe eventName
    }

    "fail when there are 2 outcome events without retry strategy" in {
      val eventName = "originalEvent1"
      val eventName2 = "originalEvent2"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(eventName2, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy = BlockInteraction

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      assertThrows[FatalInteractionException] {
        ProcessInstance.getOutputEventName(interactionTransition, logMock)
      }
    }

    "correctly determine the output event name when FireEventAfterFailure strategy is used" in {
      val eventName = "originalEvent1"
      val exhaustedEvent = "exhaustedEvent"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(exhaustedEvent, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy = FireEventAfterFailure(EventDescriptor(exhaustedEvent, Seq.empty))

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      output shouldBe eventName
    }

    "correctly determine the output event name when RetryWithIncrementalBackoff with FireEvent is used" in {
      val eventName = "originalEvent1"
      val exhaustedEvent = "exhaustedEvent"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(exhaustedEvent, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy =
        RetryWithIncrementalBackoff(Zero, 1.0, 1, Option.empty, Some(EventDescriptor(exhaustedEvent, Seq.empty)), None)

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      output shouldBe eventName
    }

    "correctly determine the output event name when RetryWithIncrementalBackoff with FireFunctionalEvent is used" in {
      val eventName = "originalEvent1"
      val exhaustedEvent = "exhaustedEvent"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(exhaustedEvent, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy =
        RetryWithIncrementalBackoff(Zero, 1.0, 1, Option.empty, Option.empty, Some(EventDescriptor(exhaustedEvent, Seq.empty)))

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      output shouldBe eventName
    }

    "correctly determine the output event name when RetryWithIncrementalBackoff without FireEvent is used" in {
      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy =
        RetryWithIncrementalBackoff(Zero, 1.0, 1, Option.empty, Option.empty, None)

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      output shouldBe eventName
    }
  }

  "ProcessInstance.getWaitTimeInMillis" should {

    "correctly extract wait time from Java Duration" in {
      val eventName = "originalEvent1"
      val waitTimeMillis = 5000L

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[Duration])),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val waitTimeDuration = Duration.ofMillis(waitTimeMillis)
      val state = RecipeInstanceState(
        recipeId = "recipeId",
        recipeInstanceId = "recipeInstanceId",
        ingredients = Map("waitTime" -> Converters.toValue(waitTimeDuration)),
        recipeInstanceMetadata = Map.empty,
        events = List.empty
      )

      val extractedWaitTime = ProcessInstance.getWaitTimeInMillis(interactionTransition, state)

      extractedWaitTime shouldBe waitTimeMillis
    }

    "correctly extract wait time from Scala FiniteDuration" in {
      val eventName = "originalEvent1"
      val waitTimeMillis = 3000L

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[FiniteDuration])),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val waitTimeDuration = FiniteDuration(waitTimeMillis, MILLISECONDS)
      val state = RecipeInstanceState(
        recipeId = "recipeId",
        recipeInstanceId = "recipeInstanceId",
        ingredients = Map("waitTime" -> Converters.toValue(waitTimeDuration)),
        recipeInstanceMetadata = Map.empty,
        events = List.empty
      )

      val extractedWaitTime = ProcessInstance.getWaitTimeInMillis(interactionTransition, state)

      extractedWaitTime shouldBe waitTimeMillis
    }

    "fail when there are more than 1 ingredient" in {
      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(
          IngredientDescriptor("waitTime", Converters.readJavaType[Duration]),
          IngredientDescriptor("otherIngredient", Converters.readJavaType[String])
        ),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val state = RecipeInstanceState(
        recipeId = "recipeId",
        recipeInstanceId = "recipeInstanceId",
        ingredients = Map(
          "waitTime" -> Converters.toValue(Duration.ofMillis(1000L)),
          "otherIngredient" -> Converters.toValue("value")
        ),
        recipeInstanceMetadata = Map.empty,
        events = List.empty
      )

      assertThrows[FatalInteractionException] {
        ProcessInstance.getWaitTimeInMillis(interactionTransition, state)
      }
    }

    "fail when the ingredient is the wrong type" in {
      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[String])),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val state = RecipeInstanceState(
        recipeId = "recipeId",
        recipeInstanceId = "recipeInstanceId",
        ingredients = Map("waitTime" -> Converters.toValue("not a duration")),
        recipeInstanceMetadata = Map.empty,
        events = List.empty
      )

      assertThrows[FatalInteractionException] {
        ProcessInstance.getWaitTimeInMillis(interactionTransition, state)
      }
    }
  }
}
