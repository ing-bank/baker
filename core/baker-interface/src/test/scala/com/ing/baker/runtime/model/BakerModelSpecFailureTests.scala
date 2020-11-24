package com.ing.baker.runtime.model

import java.util.UUID

import cats.effect.ConcurrentEffect
import cats.implicits._
import com.ing.baker.recipe.common.InteractionFailureStrategy._
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.BakerException.ProcessDeletedException
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import org.mockito.Matchers.{eq => mockitoEq, _}
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock

import scala.concurrent.duration._
import scala.reflect.ClassTag

trait BakerModelSpecFailureTests[F[_]] { self: BakerModelSpec[F] =>

  def runFailureTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {
    test("not throw an exception when an event is fired and a resulting interactions fails") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("FailingInteraction")
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionOneMock.apply(anyString, anyString()))
          .thenThrow(new RuntimeException(errorMessage))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield succeed
    }

    test("not crash when one process crashes but the other does not") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("CrashTestRecipe")
        (baker, recipeId) = bakerAndRecipeId

        firstrecipeInstanceId = UUID.randomUUID().toString
        secondrecipeInstanceId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(firstrecipeInstanceId.toString, initialIngredientValue))
          .thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
        _ = when(testInteractionOneMock.apply(secondrecipeInstanceId.toString, initialIngredientValue))
          .thenThrow(new RuntimeException(errorMessage))
        _ <- baker.bake(recipeId, firstrecipeInstanceId)
        _ <- baker.bake(recipeId, secondrecipeInstanceId)
        // start the first process with firing an event
        _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        // start the second process and expect a failure
        _ <- baker.fireEventAndResolveWhenCompleted(secondrecipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        // fire another event for the first process
        _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        // expect first process state is correct
        state <- baker.getRecipeInstanceState(firstrecipeInstanceId)
      } yield state.ingredients shouldBe finalState
    }

    test("keep the input data in accumulated state even if the interactions dependent on this event fail to execute") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("StatePersistentTestRecipe")
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(recipeInstanceId.toString, initialIngredientValue))
          .thenThrow(new RuntimeException(errorMessage))
        _ <- baker.bake(recipeId, recipeInstanceId)

        // Send failing event and after that send succeeding event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe ingredientMap(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue)
    }

    test("retry an interaction with incremental backoff when instructed to do so") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("FailingInteractionWithBackoff")
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException(errorMessage))

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        //Thread.sleep is needed since we need to wait for the exponential back-off
        //100ms should be enough since it waits 20ms and then 40 ms
        _ <- effect.delay {
          Thread.sleep(200)
        }
        //Since it can be called up to 3 times it should have been called 3 times in the 100ms
        _ = verify(testInteractionOneMock, times(4)).apply(recipeInstanceId.toString, initialIngredientValue)
      } yield succeed
    }

    test("not execute the failing interaction again each time after some other unrelated event is fired") { context =>
      /* This test FAILS because passportData FAIL_DATA is included in the marking while it should not! (?)
     * The fact that it is in the marking forces failingUploadPassport to fire again when second event fires!
     */
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("ShouldNotReExecute")
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString

        _ = when(testInteractionTwoMock.apply(anyString())).thenThrow(new RuntimeException(errorMessage))
        _ <- baker.bake(recipeId, recipeInstanceId)

        // first fired event causes a failure in the action
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionTwoMock, times(1)).apply(anyString())
        _ = resetMocks()

        // second fired, this should not re-execute InteractionOne and therefor not start InteractionThree
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        _ = verify(testInteractionTwoMock, never()).apply(anyString())
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe ingredientMap(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionOneIngredient" -> interactionOneIngredientValue)
    }

    test("fire the exhausted retry event if the max retry times for the interaction is met") { context =>

      val recipe = Recipe("FireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(RetryWithIncrementalBackoff(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          fireRetryExhaustedEvent = Some(None))))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new IllegalStateException())

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.eventNames should contain(interactionOne.retryExhaustedEventName)
    }

    test("not fire the exhausted retry event if the interaction completes") { context =>
      val recipe = Recipe("NotFireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(RetryWithIncrementalBackoff(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          fireRetryExhaustedEvent = Some(None))))


      for {
        _ <- setupMockResponse
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        //Since the defaultEventExhaustedName is set the retryExhaustedEventName of interactionOne will be picked.
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.eventNames should not contain interactionOne.retryExhaustedEventName
    }

    test("fire a specified failure event for an interaction immediately after it fails") { context =>

      val recipe = Recipe("ImmediateFailureEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(FireEventAfterFailure()))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Some failure happened"))

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId

        listenerMock = mock[(RecipeEventMetadata, EventInstance) => Unit]
        _ <- baker.registerEventListener("ImmediateFailureEvent", listenerMock)

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(listenerMock).apply(mockitoEq(RecipeEventMetadata(recipeId, recipe.name, recipeInstanceId.toString)), argThat(new RuntimeEventMatcher(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))))
        _ = verify(listenerMock).apply(mockitoEq(RecipeEventMetadata(recipeId, recipe.name, recipeInstanceId.toString)), argThat(new RuntimeEventMatcher(EventInstance(interactionOne.retryExhaustedEventName, Map.empty))))

        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.eventNames should contain(interactionOne.retryExhaustedEventName)
    }

    test("resolve a blocked interaction") { context =>
      val recipe =
        Recipe("ResolveBlockedInteractionRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Expected test failure"))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state0 <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state0.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue)
        _ <- baker.resolveInteraction(recipeInstanceId, interactionOne.name, EventInstance.unsafeFrom(InteractionOneSuccessful("success!")))
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> "success!")
    }

    test("retry a blocked interaction") { context =>
      val recipe =
        Recipe("RetryBlockedInteractionRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException("Expected test failure"))
          .thenReturn(effect.pure(InteractionOneSuccessful("success!")))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state0 <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state0.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue)
        _ <- baker.retryInteraction(recipeInstanceId, interactionOne.name)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> "success!")
    }

    test("be able to return when all occurred events") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("CheckEventRecipe")
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        //Check if both the new event and the events occurred in the past are in the eventsList
        state0 <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state0.eventNames should contain only(
          "InitialEvent",
          "SieveInteractionSuccessful",
          "EventFromInteractionTwo",
          "InteractionOneSuccessful",
          "InteractionThreeSuccessful"
        )
        //Execute another event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        //Check if both the new event and the events occurred in the past are in the eventsList
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.eventNames should contain only(
        "InitialEvent",
        "EventFromInteractionTwo",
        "SecondEvent",
        "InteractionOneSuccessful",
        "SieveInteractionSuccessful",
        "InteractionThreeSuccessful",
        "InteractionFourSuccessful"
      )
    }

    test("acknowledge the first event, not wait on the rest") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("NotWaitForTheRest")
        (baker, recipeId) = bakerAndRecipeId
        interaction2Delay = 2000
        _ = when(testInteractionTwoMock.apply(anyString())).thenAnswer {
          _: InvocationOnMock => {
            Thread.sleep(interaction2Delay)
            interactionTwoEventValue
          }
        }
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
    }

    test("acknowledge the first and final event while rest processing failed") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("AcknowledgeThefirst")
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionTwoMock.apply(anyString()))
          .thenThrow(new RuntimeException("Unknown Exception.")) // This interaction is not retried and blocks the process
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        response = baker.fireEvent(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        received <- response.resolveWhenReceived
        _ = received shouldBe SensoryEventStatus.Received
        completed <- response.resolveWhenCompleted
        // The process is completed because it is in a BLOCKED state
        _ = completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
      } yield succeed
    }

    test("bind multi transitions correctly even if ingredient name overlaps") { context =>
      //This test is part of the ExecutionSpec and not the Compiler spec because the only correct way to validate
      //for this test is to check if Baker calls the mocks.
      //If there is a easy way to validate the created petrinet by the compiler it should be moved to the compiler spec.
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("OverlappingMultiIngredients")
        (baker, recipeId) = bakerAndRecipeId

        // It is helpful to check the recipe visualization if this test fails
        //      println(baker.compiledRecipe.getRecipeVisualization)

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testInteractionOneMock, times(1)).apply(recipeInstanceId.toString, initialIngredientValue)
        _ = verify(testInteractionTwoMock, times(1)).apply(initialIngredientValue)
        _ = verifyNoMoreInteractions(testInteractionFiveMock, testInteractionSixMock)
      } yield succeed
    }

    test("be able to use the same ingredient multiple times as input parameter for an interaction") { context =>
      val recipe: Recipe =
        Recipe("sameIngredientMultipleTime")
          .withInteractions(
            interactionOne,
            interactionThree
              .withOverriddenIngredientName("interactionOneIngredient", "interactionOneOriginalIngredient")
              .withOverriddenIngredientName("interactionTwoIngredient", "interactionOneOriginalIngredient"))
          .withSensoryEvents(initialEvent)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
        _ = when(testInteractionThreeMock.apply(anyString(), anyString())).thenReturn(InteractionThreeSuccessful(interactionThreeIngredientValue))

        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock, times(1)).apply(recipeInstanceId.toString, initialIngredientValue)
        _ = verify(testInteractionThreeMock, times(1)).apply(interactionOneIngredientValue, interactionOneIngredientValue)
      } yield succeed
    }

    test("reject sensory events after a specified receive period") { context =>

      val receivePeriod: FiniteDuration = 100 milliseconds

      val recipe: Recipe =
        Recipe("eventReceiveExpirationRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- effect.delay {
          Thread.sleep(receivePeriod.toMillis + 100)
        }
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
        _ = completed.sensoryEventStatus shouldBe SensoryEventStatus.ReceivePeriodExpired
      } yield succeed
    }

    test("accept sensory events before a specified receive period") { context =>

      val receivePeriod: FiniteDuration = 10 seconds

      val recipe: Recipe =
        Recipe("eventReceiveInTimeRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
      } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
    }

    test("block interaction and log error message when a null ingredient is provided by an event provided by an interaction") { context =>
      val recipe =
        Recipe("NullIngredientFromEventRecipe")
          .withInteraction(interactionTwo
            .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"))
          .withSensoryEvent(initialEvent)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionTwoMock.apply(anyString())).thenReturn(EventFromInteractionTwo(null))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionTwoMock).apply("initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
      } yield succeed
    }
  }
}
