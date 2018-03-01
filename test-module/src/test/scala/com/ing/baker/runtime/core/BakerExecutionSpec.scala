package com.ing.baker.runtime.core

import java.util.concurrent.TimeUnit
import java.util.{Optional, UUID}

import akka.actor.ActorSystem
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.{TestDuration, TestKit, TestProbe}
import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure
import com.ing.baker.recipe.scaladsl.{Recipe, _}
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock
import org.mockito.stubbing.Answer
import org.scalatest.time.{Milliseconds, Span}
import org.slf4j.LoggerFactory

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.util.Success

case class SomeNotDefinedEvent(name: String)

class BakerExecutionSpec extends TestRecipeHelper {

  override def actorSystemName = "BakerExecutionSpec"

  val log = LoggerFactory.getLogger(classOf[BakerExecutionSpec])


  before {
    resetMocks
    setupMockResponse()

    // Clean inmemory-journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(defaultActorSystem).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

  "The Baker execution engine" should {

    "bake a process successful if baking for the first time" in {
      val (baker, recipeId) = setupBakerWithRecipe("FirstTimeBaking")

      val id = UUID.randomUUID().toString
      baker.bake(recipeId, id)
    }

    "throw an IllegalArgumentException if a baking a process with the same identifier twice" in {
      val (baker, recipeId) = setupBakerWithRecipe("DuplicateIdentifierRecipe")

      val id = UUID.randomUUID().toString
      baker.bake(recipeId, id)
      a[IllegalArgumentException] should be thrownBy {
        baker.bake(recipeId, id)
      }
    }

    "throw a NoSuchProcessException when requesting the ingredients of a non existing process" in {

      val (baker, recipeId) = setupBakerWithRecipe("NonExistingProcessTest")

      intercept[NoSuchProcessException] {
        baker.getIngredients(UUID.randomUUID().toString)
      }
    }

    "throw a NoSuchProcessException when attempting to fire an event for a non existing process" in {
      val (baker, recipeId) = setupBakerWithRecipe("NonExistingProcessEventTest")

      val event = InitialEvent("initialIngredient")

      intercept[NoSuchProcessException] {
        baker.processEvent(UUID.randomUUID().toString, event)
      }

      val response = baker.processEventAsync(UUID.randomUUID().toString, event)

      intercept[NoSuchProcessException] {
        Await.result(response.receivedFuture, timeout)
      }

      intercept[NoSuchProcessException] {
        Await.result(response.completedFuture, timeout)
      }
    }

    "throw a IllegalArgumentException if fired event is not a valid sensory event" in {
      val (baker, recipeId) = setupBakerWithRecipe("NonExistingProcessEventTest")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      val intercepted: IllegalArgumentException = intercept[IllegalArgumentException] {
        baker.processEvent(processId, SomeNotDefinedEvent("bla"))
      }
      intercepted.getMessage should startWith("No event with name 'SomeNotDefinedEvent' found in recipe 'NonExistingProcessEventTest")
    }

    "execute an interaction when its ingredient is provided" in {
      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "only allow a sensory event be fired once if the max firing limit is set one" in {
      val recipe =
        Recipe("maxFiringLimitOfOneOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(1))

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      val executedFirst = baker.processEvent(processId, InitialEvent(initialIngredientValue))
      executedFirst shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

      val executedSecond = baker.processEvent(processId, InitialEvent(initialIngredientValue))
      executedSecond shouldBe SensoryEventStatus.FiringLimitMet
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
    }


    "not allow a sensory event be fired twice with the same correlation id" in {
      val recipe =
        Recipe("correlationIdSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      val executedFirst = baker.processEvent(processId, InitialEvent(initialIngredientValue), Some("abc"))
      executedFirst shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

      val executedSecond = baker.processEvent(processId, InitialEvent(initialIngredientValue), Some("abc"))
      executedSecond shouldBe SensoryEventStatus.AlreadyReceived
      verifyNoMoreInteractions(testInteractionOneMock)
    }


    "only allow a sensory event be fired twice if the max firing limit is set two" in {
      val recipe =
        Recipe("maxFiringLimitOfTwoOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(2))

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      val executedFirst = baker.processEvent(processId, InitialEvent(initialIngredientValue))
      executedFirst shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

      val executedSecond = baker.processEvent(processId, InitialEvent(initialIngredientValue))
      executedSecond shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")

      // This check is added to verify event list is still correct after firing the same event twice
      baker.events(processId).map(_.name).toList shouldBe List("InitialEvent", "InteractionOneSuccessful", "InitialEvent", "InteractionOneSuccessful")

      val executedThird = baker.processEvent(processId, InitialEvent(initialIngredientValue))
      executedThird shouldBe SensoryEventStatus.FiringLimitMet
      verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")
    }

    "backwards compatibility in serialization of case class ingredients" ignore {
      val tmpDir = System.getProperty("java.io.tmpdir")
      val journalPath = tmpDir + "/journal"
      val snapshotsPath = tmpDir + "/snapshots"
      val processId = "test-process-5"

      val actorSystem = ActorSystem("backwardsCompatibilityOfEvents", levelDbConfig("backwardsCompatibilityOfEvents", 3004, 10 seconds, journalPath, snapshotsPath))
      val recoveryRecipeName = "backwardsCompatibilityOfEvents"

      try {
        val recipe =
          Recipe(recoveryRecipeName)
            .withInteraction(caseClassIngredientInteraction)
            .withInteraction(caseClassIngredientInteraction2)
            .withSensoryEvent(initialEvent)

        val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

        // Bake a new recipe, fire initial event. 2nd time baking with the same processId fails, so comment this part out after creating the process
        baker.bake(recipeId, processId)

        when(testCaseClassIngredientInteractionMock.apply(anyString())).thenReturn(caseClassIngredientValue)
        when(testCaseClassIngredientInteraction2Mock.apply(any[CaseClassIngredient]())).thenReturn(EmptyEvent())

        verify(testCaseClassIngredientInteractionMock).apply(initialIngredientValue)
        verify(testCaseClassIngredientInteraction2Mock).apply(caseClassIngredientValue)
        baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue, "caseClassIngredient" -> caseClassIngredientValue)
        // Process creation finished

        // check if events/ingredients are ok
      } finally {
        TestKit.shutdownActorSystem(actorSystem)
      }
    }

    "execute an interaction with Optionals set to empty when its ingredient is provided" in {
      val ingredientValue: Optional[String] = java.util.Optional.of("optionalWithValue")

      val recipe =
        Recipe("IngredientProvidedRecipeWithEmptyOptionals")
          .withInteraction(
            optionalIngredientInteraction
              .withPredefinedIngredients(("missingJavaOptional", ingredientValue)))
          .withSensoryEvent(initialEvent)

      val baker = new Baker()

      baker.addInteractionImplementations(mockImplementations)

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val recipeId = baker.addRecipe(compiledRecipe)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId).toString

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testOptionalIngredientInteractionMock).apply(ingredientValue, Optional.empty(), Option.empty, Option.empty, initialIngredientValue)
      baker.getIngredients(processId) shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
    }

    "execute an interaction with Optionals boxed when its ingredient is provided as unboxed" in {

      val recipe =
        Recipe("IngredientProvidedRecipeWithUnboxedOptionals")
          .withInteraction(
            optionalIngredientInteraction)
          .withSensoryEvent(unboxedProviderEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId).toString
      baker.processEvent(processId, UnboxedProviderEvent(initialIngredientValue, initialIngredientValue, initialIngredientValue))

      verify(testOptionalIngredientInteractionMock).apply(java.util.Optional.of(initialIngredientValue), Optional.empty(), Some(initialIngredientValue), Option.empty, initialIngredientValue)
      baker.getIngredients(processId) shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "missingJavaOptional" -> initialIngredientValue, "missingScalaOptional" -> initialIngredientValue)
    }

    "notify a registered event listener of events" in {

      val listenerMock = mock[EventListener]

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val recipe =
        Recipe("EventListenerRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      baker.registerEventListener("EventListenerRecipe", listenerMock)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(listenerMock).processEvent(processId.toString, RuntimeEvent.create("InitialEvent", Seq("initialIngredient" -> initialIngredientValue)))
      verify(listenerMock).processEvent(processId.toString, RuntimeEvent.create("InteractionOneSuccessful", Seq("interactionOneOriginalIngredient" -> interactionOneIngredientValue)))
    }

    "execute an interaction when its ingredient is provided and the interaction is renamed" in {
      val recipe =
        Recipe("IngredientProvidedRecipeWithRename")
          .withInteraction(interactionOne, "interactionOneRenamed")
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "execute an interaction when both ingredients are provided (join situation)" in {
      val (baker, recipeId) = setupBakerWithRecipe("JoinRecipeForIngredients")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)
      verify(testInteractionTwoMock).apply(initialIngredientValue)
      verify(testInteractionThreeMock).apply(interactionOneIngredientValue, interactionTwoIngredientValue)
      baker.getIngredients(processId) shouldBe afterInitialState
    }

    "execute an interaction when two events occur (join situation)" in {
      val (baker, recipeId) = setupBakerWithRecipe("JoinRecipeForEvents")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent("initialIngredient"))
      baker.processEvent(processId, SecondEvent())

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock).apply("initialIngredient")
      verify(testInteractionThreeMock).apply("interactionOneIngredient",
        "interactionTwoIngredient")
      verify(testInteractionFourMock).apply()
      baker.getIngredients(processId) shouldBe finalState
    }

    "execute an interaction when one of the two events occur (OR situation)" in {
      val recipe = Recipe("ORPreconditionedRecipeForEvents")
        .withInteractions(interactionFour
          .withRequiredOneOfEvents(initialEvent, secondEvent))
        .withSensoryEvents(initialEvent, secondEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val firstProcessId = UUID.randomUUID().toString
      baker.bake(recipeId, firstProcessId)

      // Fire one of the events for the first process
      baker.processEvent(firstProcessId, InitialEvent("initialIngredient"))
      verify(testInteractionFourMock).apply()

      // reset interaction mocks and fire the other event for the second process
      resetMocks

      val secondProcessId = UUID.randomUUID().toString
      baker.bake(recipeId, secondProcessId)

      baker.processEvent(secondProcessId, SecondEvent())
      verify(testInteractionFourMock).apply()
    }

    "execute an interaction when one of the two events occur with two or conditions (OR situation 2)" in {
      val recipe = Recipe("ORPreconditionedRecipeForEvents2")
        .withInteractions(interactionFour
          .withRequiredOneOfEvents(initialEvent, secondEvent)
          .withRequiredOneOfEvents(thirdEvent, fourthEvent))
        .withSensoryEvents(initialEvent, secondEvent, thirdEvent, fourthEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val firstProcessId = UUID.randomUUID().toString
      baker.bake(recipeId, firstProcessId)

      // Fire one of the events for the first process
      baker.processEvent(firstProcessId, InitialEvent("initialIngredient"))
      verify(testInteractionFourMock, times(0)).apply()

      baker.processEvent(firstProcessId, ThirdEvent())
      verify(testInteractionFourMock).apply()
    }

    "execute two interactions which depend on same ingredient (fork situation)" in {

      val (baker, recipeId) = setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent("initialIngredient"))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock).apply("initialIngredient")
    }

    "execute again after first execution completes and ingredient is produced again" in {

      val (baker, recipeId) = setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent("initialIngredient"))

      verify(testInteractionOneMock, times(1)).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock, times(1)).apply("initialIngredient")

      baker.processEvent(processId, InitialEvent("initialIngredient"))

      verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock, times(2)).apply("initialIngredient")
    }

    "fire parallel transitions simultaneously" in {

      val (baker, recipeId) = setupBakerWithRecipe("ParallelExecutionRecipe")

      // Two answers that take 0.5 seconds each!
      when(testInteractionOneMock.apply(anyString(), anyString())).thenAnswer(new Answer[String] {
        override def answer(invocationOnMock: InvocationOnMock): String = {
          Thread.sleep(500)
          interactionOneIngredientValue
        }
      })

      when(testInteractionTwoMock.apply(anyString()))
        .thenAnswer(new Answer[EventFromInteractionTwo] {
          override def answer(invocationOnMock: InvocationOnMock): EventFromInteractionTwo = {
            Thread.sleep(500)
            EventFromInteractionTwo(interactionTwoIngredientValue)
          }
        })

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      Thread.sleep(2000)

      val executingTimeInMilliseconds = timeBlockInMilliseconds {
        baker.processEvent(processId, InitialEvent(initialIngredientValue))
      }

      val tookLessThanASecond = executingTimeInMilliseconds < 1000
      assert(
        tookLessThanASecond,
        s"If it takes less than one second to execute we can be sure the two actions have executed in parallel. " +
          s"The execution took: $executingTimeInMilliseconds milliseconds and have executed sequentially...")
      // Note: this is not related to startup time.
      // Same behaviour occurs if we have actions that take 10 seconds and test if it is less than 20 seconds.
    }

    "update the state with new data if an event occurs twice" in {

      val firstData: String = "firstData"
      val secondData: String = "secondData"
      val firstResponse = "firstResponse"
      val secondResponse = "secondResponse"

      val (baker, recipeId) = setupBakerWithRecipe("UpdateTestRecipe")

      val processId = UUID.randomUUID().toString

      when(testInteractionOneMock.apply(processId.toString, firstData)).thenReturn(firstResponse)
      when(testInteractionOneMock.apply(processId.toString, secondData)).thenReturn(secondResponse)

      baker.bake(recipeId, processId)

      //Fire the first event
      baker.processEvent(processId, InitialEvent(firstData))

      //Check that the first response returned
      baker.getIngredients(processId) shouldBe ingredientMap(
        "initialIngredient" -> firstData,
        "interactionOneIngredient" -> firstResponse,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue,
        "interactionThreeIngredient" -> interactionThreeIngredientValue
      )

      //Fire the second event
      baker.processEvent(processId, InitialEvent(secondData))

      //Check that the second response is given
      baker.getIngredients(processId) shouldBe ingredientMap(
        "initialIngredient" -> secondData,
        "interactionOneIngredient" -> secondResponse,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue,
        "interactionThreeIngredient" -> interactionThreeIngredientValue
      )
    }

    "only fire an interaction once if it has an maximum interaction count of 1" in {

      val recipe = Recipe("FiringLimitTestRecipe")
        .withInteractions(
          interactionOne
            .withOverriddenOutputIngredientName("interactionOneIngredient")
            .withMaximumInteractionCount(1))
        .withSensoryEvent(initialEvent)

      when(testInteractionOneMock.apply(anyString(), anyString()))
        .thenReturn(interactionOneIngredientValue)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)

      val result = baker.getIngredients(processId)
      result shouldBe ingredientMap(
        "initialIngredient" -> initialIngredientValue,
        "interactionOneIngredient" -> interactionOneIngredientValue)

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verifyZeroInteractions(testInteractionOneMock)
    }

    "not throw an exception when an event is fired and a resulting interactions fails" in {
      val (baker, recipeId) = setupBakerWithRecipe("FailingInteraction")
      when(testInteractionOneMock.apply(anyString, anyString()))
        .thenThrow(new RuntimeException(errorMessage))

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))
    }

    "not crash when one process crashes but the other does not" in {

      val (baker, recipeId) = setupBakerWithRecipe("CrashTestRecipe")

      val firstProcessId = UUID.randomUUID().toString
      val secondProcessId = UUID.randomUUID().toString
      when(testInteractionOneMock.apply(firstProcessId.toString, initialIngredientValue))
        .thenReturn(interactionOneIngredientValue)
      when(testInteractionOneMock.apply(secondProcessId.toString, initialIngredientValue))
        .thenThrow(new RuntimeException(errorMessage))
      baker.bake(recipeId, firstProcessId)
      baker.bake(recipeId, secondProcessId)

      // start the first process with firing an event
      baker.processEvent(firstProcessId, InitialEvent(initialIngredientValue))

      // start the second process and expect a failure
      baker.processEvent(secondProcessId, InitialEvent(initialIngredientValue))

      // fire another event for the first process
      baker.processEvent(firstProcessId, SecondEvent())

      // expect first process state is correct
      baker.getIngredients(firstProcessId) shouldBe finalState
    }

    "keep the input data in accumulated state even if the interactions dependent on this event fail to execute" in {

      val (baker, recipeId) = setupBakerWithRecipe("StatePersistentTestRecipe")
      val processId = UUID.randomUUID().toString
      when(testInteractionOneMock.apply(processId.toString, initialIngredientValue))
        .thenThrow(new RuntimeException(errorMessage))
      baker.bake(recipeId, processId)

      // Send failing event and after that send succeeding event
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      val result = baker.getIngredients(processId)
      result shouldBe ingredientMap(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue)
    }

    "retry an interaction with incremental backoff if configured to do so" in {

      val (baker, recipeId) = setupBakerWithRecipe("FailingInteractionWithBackof")
      when(testInteractionOneMock.apply(anyString(), anyString()))
        .thenThrow(new RuntimeException(errorMessage))

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      //Thread.sleep is needed since we need to wait for the expionental back of
      //100ms should be enough since it waits 20ms and then 40 ms
      Thread.sleep(200)
      //Since it can be called up to 3 times it should have been called 3 times in the 100ms
      verify(testInteractionOneMock, times(4)).apply(processId.toString, initialIngredientValue)
    }

    "not execute the failing interaction again each time after some other unrelated event is fired" in {

      /* This test FAILS because passportData FAIL_DATA is included in the marking while it should not! (?)
       * The fact that it is in the marking forces failingUploadPassport to fire again when second event fires!
       */
      val (baker, recipeId) = setupBakerWithRecipe("ShouldNotReExecute")
      val processId = UUID.randomUUID().toString

      when(testInteractionTwoMock.apply(anyString())).thenThrow(new RuntimeException(errorMessage))
      baker.bake(recipeId, processId)

      // first fired event causes a failure in the action
      baker.processEvent(processId, InitialEvent(initialIngredientValue))
      verify(testInteractionTwoMock, times(1)).apply(anyString())
      resetMocks

      // second fired, this should not re-execute InteractionOne and therefor not start InteractionThree
      baker.processEvent(processId, SecondEvent())

      verify(testInteractionTwoMock, never()).apply(anyString())

      val result = baker.getIngredients(processId)
      result shouldBe ingredientMap(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionOneIngredient" -> interactionOneIngredientValue)
    }

    "fire the exhausted retry event if the max retry times for the interaction is met" in {

      val recipe = Recipe("FireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          fireRetryExhaustedEvent = Some(None))))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new BakerException())

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      //Handle first event
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      Thread.sleep(50)

      baker.events(processId).map(_.name) should contain(interactionOne.retryExhaustedEventName)
    }

    "not fire the exhausted retry event if the interaction passes" in {
      val recipe = Recipe("NotFireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          fireRetryExhaustedEvent = Some(None))))

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      //Handle first event
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      Thread.sleep(50)

      //Since the defaultEventExhaustedName is set the retryExhaustedEventName of interactionOne will be picked.
      baker.events(processId).map(_.name) should not contain interactionOne.retryExhaustedEventName
    }

    "fire a specified failure event for an interaction immediately after it fails" in {

      val recipe = Recipe("ImmediateFailureEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(FireEventAfterFailure()))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Some failure happened"))

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val listenerMock = mock[EventListener]
      baker.registerEventListener("ImmediateFailureEvent", listenerMock)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      //Handle first event
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      Thread.sleep(50)
      verify(listenerMock).processEvent(processId.toString, RuntimeEvent.create("InitialEvent", Seq("initialIngredient" -> initialIngredientValue)))
      verify(listenerMock).processEvent(processId.toString, RuntimeEvent.create(interactionOne.retryExhaustedEventName, Seq.empty))

      baker.events(processId).map(_.name) should contain(interactionOne.retryExhaustedEventName)
    }

    "be able to return all occurred events" in {

      val (baker, recipeId) = setupBakerWithRecipe("CheckEventRecipe")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      //Handle first event
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      //Check if both the new event and the events occurred in the past are in the eventsList
      baker.events(processId) should contain only(
        RuntimeEvent.create("InitialEvent", Seq("initialIngredient" -> initialIngredientValue)),
        RuntimeEvent.create("SieveInteractionSuccessful", Seq("sievedIngredient" -> sievedIngredientValue)),
        RuntimeEvent.create("EventFromInteractionTwo", Seq("interactionTwoIngredient" -> interactionTwoIngredientValue)),
        RuntimeEvent.create("InteractionOneSuccessful", Seq("interactionOneIngredient" -> interactionOneIngredientValue)),
        RuntimeEvent.create("InteractionThreeSuccessful", Seq("interactionThreeIngredient" -> interactionThreeIngredientValue))
      )

      //Execute another event
      baker.processEvent(processId, SecondEvent())

      //Check if both the new event and the events occurred in the past are in the eventsList
      baker.events(processId) should contain only(
        RuntimeEvent.create("InitialEvent", Seq("initialIngredient" -> "initialIngredient")),
        RuntimeEvent.create("EventFromInteractionTwo", Seq("interactionTwoIngredient" -> "interactionTwoIngredient")),
        RuntimeEvent.create("SecondEvent", Seq.empty),
        RuntimeEvent.create("InteractionOneSuccessful", Seq("interactionOneIngredient" -> interactionOneIngredientValue)),
        RuntimeEvent.create("SieveInteractionSuccessful", Seq("sievedIngredient" -> sievedIngredientValue)),
        RuntimeEvent.create("InteractionThreeSuccessful", Seq("interactionThreeIngredient" -> interactionThreeIngredientValue)),
        RuntimeEvent.create("InteractionFourSuccessful", Seq("interactionFourIngredient" -> interactionFourIngredientValue))
      )
    }

    "be able to return all occurred event names" in {

      val (baker, recipeId) = setupBakerWithRecipe("CheckEventNamesRecipe")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      //Handle two event
      baker.processEvent(processId, InitialEvent(initialIngredientValue))
      baker.processEvent(processId, SecondEvent())

      //Check if both the new event and the events occurred in the past are in the eventsList
      baker.eventNames(processId) should contain only(
        "InitialEvent",
        "EventFromInteractionTwo",
        "SecondEvent",
        "InteractionOneSuccessful",
        "SieveInteractionSuccessful",
        "InteractionThreeSuccessful",
        "InteractionFourSuccessful"
      )
    }

    //Only works if persistence actors are used (think cassandra)
    "recover the state of a process from a persistence store" in {
      val system1 = ActorSystem("persistenceTest1", levelDbConfig("persistenceTest1", 3002))
      val recoveryRecipeName = "RecoveryRecipe"
      val processId = UUID.randomUUID().toString

      var recipeId: String = ""
      val compiledRecipe = RecipeCompiler.compileRecipe(getComplexRecipe(recoveryRecipeName))

      try {
        val baker1 = setupBakerWithNoRecipe()(system1)
        recipeId = baker1.addRecipe(compiledRecipe)
        baker1.bake(recipeId, processId)
        baker1.processEvent(processId, InitialEvent(initialIngredientValue))
        baker1.processEvent(processId, SecondEvent())
        baker1.getIngredients(processId) shouldBe finalState
      } finally {
        TestKit.shutdownActorSystem(system1)
      }

      val system2 = ActorSystem("persistenceTest2", levelDbConfig("persistenceTest2", 3003))
      try {
        val baker2 = new Baker()(system2)
        baker2.addInteractionImplementations(mockImplementations)
        baker2.getIngredients(processId) shouldBe finalState
        baker2.getRecipe(recipeId) shouldBe compiledRecipe
        baker2.addRecipe(compiledRecipe) shouldBe recipeId
      } finally {
        TestKit.shutdownActorSystem(system2)
      }
    }

    //    "do not join to akka cluster and fail to bootstrap if persistence init actor times out" in {
    //      val recipeName = "lazyClusterJoinTest"
    //      val persistenceInitDuration = 3 seconds
    //      val journalInitializeTimeout = 2 seconds
    //      val actorSystem = ActorSystem(recipeName, levelDbConfig(recipeName, 3005, journalInitializeTimeout))
    //
    //      val persistenceInitActorProps = Props(new Actor() {
    //        override def receive = {
    //          case msg =>
    //            Thread.sleep(persistenceInitDuration.toMillis)
    //            sender() ! msg
    //            context.stop(self)
    //        }
    //      })
    //
    //      intercept[TimeoutException] {
    //        try {
    //          setupBakerWithRecipe(recipeName, appendUUIDToTheRecipeName = false, persistenceInitActorProps)(actorSystem)
    //        } finally {
    //          TestKit.shutdownActorSystem(actorSystem)
    //        }
    //      }
    //
    //    }
    //
    //    "join to akka cluster after the persistence init actor returns within predefined timeout config" in {
    //      val recipeName = "lazyClusterJoinTest"
    //      val persistenceInitDuration = 2 seconds
    //      val journalInitializeTimeout = 3 seconds
    //      val actorSystem1 = ActorSystem(recipeName, levelDbConfig(recipeName, 3005, journalInitializeTimeout))
    //      val lock = new ReentrantLock()
    //
    //      println("system1 init members: " + Cluster(actorSystem1).state.members)
    ////      println("system2 init members: " + Cluster(actorSystem2).state.members)
    //
    //      def persistenceInitActorProps = Props(new Actor() {
    //        override def receive = {
    //          case msg =>
    //            lock.lock()
    //            Thread.sleep(persistenceInitDuration.toMillis)
    //            sender() ! msg
    //            lock.unlock()
    //            context.stop(self)
    //        }
    //      })
    //
    //      try {
    //        setupBakerWithRecipe(recipeName, appendUUIDToTheRecipeName = false, persistenceInitActorProps)(actorSystem1)
    //        println("system1 members after first node: " + Cluster(actorSystem1).state.members)
    ////        println("system2 members after first node: " + Cluster(actorSystem2).state.members)
    //
    //        val actorSystem2 = ActorSystem(recipeName, levelDbConfig(recipeName, 3006, journalInitializeTimeout))
    //        try {
    //          lock.lock()
    //          setupBakerWithRecipe(recipeName, appendUUIDToTheRecipeName = false, persistenceInitActorProps)(actorSystem2)
    //        } catch {
    //          case _: TimeoutException =>
    //            println("system1 after timeout members: " + Cluster(actorSystem1).state.members)
    //            println("system2 after timeout members: " + Cluster(actorSystem2).state.members)
    //            TestKit.shutdownActorSystem(actorSystem2)
    //          case e: Exception => fail("Unexpected exception here: " + e.getMessage)
    //        }
    //
    //        val actorSystem3 = ActorSystem(recipeName, levelDbConfig(recipeName, 3007, journalInitializeTimeout))
    //        try {
    //          lock.unlock()
    //          setupBakerWithRecipe(recipeName, appendUUIDToTheRecipeName = false, persistenceInitActorProps)(actorSystem3)
    //          println("system1 members: " + Cluster(actorSystem1).state.members)
    //          println("system3 members: " + Cluster(actorSystem3).state.members)
    //        } finally {
    //          TestKit.shutdownActorSystem(actorSystem3)
    //        }
    //      } finally {
    //        TestKit.shutdownActorSystem(actorSystem1)
    //      }
    //
    //    }

    "when acknowledging the first event, not wait on the rest" in {
      val (baker, recipeId) = setupBakerWithRecipe("NotWaitForTheRest")

      val interaction2Delay = 2000

      when(testInteractionTwoMock.apply(anyString())).thenAnswer {
        new Answer[EventFromInteractionTwo] {
          override def answer(invocation: InvocationOnMock): EventFromInteractionTwo = {
            Thread.sleep(interaction2Delay)
            interactionTwoEventValue
          }
        }
      }

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      val response = baker.processEventAsync(processId, InitialEvent(initialIngredientValue))

      import org.scalatest.concurrent.Timeouts._

      failAfter(Span(500, Milliseconds)) {
        Await.result(response.receivedFuture, 500 millis)
        response.completedFuture.isCompleted shouldEqual false
      }

      Await.result(response.completedFuture, 3000 millis)

      response.completedFuture.value should matchPattern { case Some(Success(_)) => }
    }

    "acknowledge the first and final event while rest processing failed" in {
      val (baker, recipeId) = setupBakerWithRecipe("AcknowledgeThefirst")

      when(testInteractionTwoMock.apply(anyString()))
        .thenThrow(new RuntimeException("Unknown Exception."))

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      val response = baker.processEventAsync(processId, InitialEvent(initialIngredientValue))
      Await.result(response.completedFuture, 3 seconds)
      response.receivedFuture.value shouldBe Some(Success(InteractionResponse.Success))
      response.completedFuture.value shouldBe Some(Success(InteractionResponse.Failed))

      response.confirmReceived() shouldBe SensoryEventStatus.Received
      response.confirmCompleted() shouldBe SensoryEventStatus.Completed
    }

    "bind multi transitions correctly even if ingredient name overlaps" in {
      //This test is part of the ExecutionSpec and not the Compiler spec because the only correct way to validate
      //for this test is to check if Baker calls the mocks.
      //If there is a easy way to validate the created petrinet by the compiler it should be moved to the compiler spec.
      val (baker, recipeId) = setupBakerWithRecipe("OverlappingMultiIngredients")

      // It is helpful to check the recipe visualization if this test fails
      //      println(baker.compiledRecipe.getRecipeVisualization)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock, times(1)).apply(processId.toString, initialIngredientValue)
      verify(testInteractionTwoMock, times(1)).apply(initialIngredientValue)
      verifyNoMoreInteractions(testInteractionFiveMock, testInteractionSixMock)
    }

    "be able to use the same ingredient multiple times as input parameter for an interaction" in {
      val recipe: Recipe =
        "sameIngredientMultipleTime"
          .withInteractions(
            interactionOne,
            interactionThree
              .withOverriddenIngredientName("interactionOneIngredient", "interactionOneOriginalIngredient")
              .withOverriddenIngredientName("interactionTwoIngredient", "interactionOneOriginalIngredient"))
          .withSensoryEvents(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)
      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock, times(1)).apply(processId.toString, initialIngredientValue)
      verify(testInteractionThreeMock, times(1)).apply(interactionOneIngredientValue, interactionOneIngredientValue)
    }

    "reject sensory events after a specified receive period" in {

      val receivePeriod: FiniteDuration = 100 milliseconds

      val recipe: Recipe =
        "eventReceiveExpirationRecipe"
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      Thread.sleep(receivePeriod.toMillis + 100)

      baker.processEvent(processId, InitialEvent("")) shouldBe SensoryEventStatus.ReceivePeriodExpired
    }

    "accept sensory events before a specified receive period" in {

      val receivePeriod: FiniteDuration = 10 seconds

      val recipe: Recipe =
        "eventReceiveInTimeRecipe"
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)
      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent("")) shouldBe SensoryEventStatus.Completed
    }

    "be able to visualize events that have been fired" in {
      //This test only checks if the graphviz is different, not that the outcome is correct
      val (baker, recipeId) = setupBakerWithRecipe("CheckEventRecipe")

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)

      val noEventsGraph = baker.getVisualState(processId)
      //      System.out.println(noEventsGraph)

      //Handle first event
      baker.processEvent(processId, InitialEvent("initialIngredient"))

      val firstEventGraph = baker.getVisualState(processId)
      //      System.out.println(firstEventGraph)

      noEventsGraph should not be firstEventGraph

      baker.processEvent(processId, SecondEvent())
      val secondEventGraph = baker.getVisualState(processId)
      //      System.out.println(secondEventGraph)

      firstEventGraph should not be secondEventGraph
    }

    "properly handle a retention period" in {

      val retentionPeriod = 2 seconds

      val recipe: Recipe =
        "RetentionPeriodRecipe"
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withRetentionPeriod(retentionPeriod)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      //Should not fail
      baker.getIngredients(processId)

      baker.events(processId)

      Thread.sleep(FiniteDuration(retentionPeriod.toMillis + 1000, TimeUnit.MILLISECONDS).dilated.toMillis)

      //Should fail
      intercept[ProcessDeletedException] {
        baker.getIngredients(processId)
      }

      intercept[ProcessDeletedException] {
        baker.events(processId)
      }
    }

    "block interaction and log error message if a null ingredient is provided directly by a Interaction" in {
      val recipe =
        Recipe("NullIngredientRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(null)

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
    }

    "block interaction and log error message if a null ingredient is provided by an Event provided by a Interaction" in {
      val recipe =
        Recipe("NullIngredientFromEventRecipe")
          .withInteraction(interactionTwo
            .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"))
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionTwoMock.apply(anyString())).thenReturn(EventFromInteractionTwo(null))

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionTwoMock).apply("initialIngredient")
      baker.getIngredients(processId) shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
    }
  }
}
