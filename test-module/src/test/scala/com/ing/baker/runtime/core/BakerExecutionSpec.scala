package com.ing.baker.runtime.core

import java.util.{Optional, UUID}

import akka.actor.ActorSystem
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.{TestKit, TestProbe}
import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
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
  implicit val timeout: FiniteDuration = 10 seconds

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
      val baker = setupBakerWithRecipe("FirstTimeBaking")

      val id = UUID.randomUUID().toString
      baker.bake(id)
    }

    "throw an IllegalArgumentException if a baking a process with the same identifier twice" in {
      val baker = setupBakerWithRecipe("DuplicateIdentifierRecipe")

      val id = UUID.randomUUID().toString
      baker.bake(id)
      a[IllegalArgumentException] should be thrownBy {
        baker.bake(id)
      }
    }

    "throw a NoSuchProcessException when requesting the ingredients of a non existing process" in {

      val baker = setupBakerWithRecipe("NonExistingProcessTest")

      intercept[NoSuchProcessException] {
        baker.getIngredients(UUID.randomUUID().toString)
      }
    }

    "throw a NoSuchProcessException when attempting to fire an event for a non existing process" in {
      val baker = setupBakerWithRecipe("NonExistingProcessEventTest")

      val event = InitialEvent("initialIngredient")

      intercept[NoSuchProcessException] {
        baker.handleEvent(UUID.randomUUID().toString, event)
      }

      val response = baker.handleEventAsync(UUID.randomUUID().toString, event)

      intercept[NoSuchProcessException] {
        Await.result(response.receivedFuture, timeout)
      }

      intercept[NoSuchProcessException] {
        Await.result(response.completedFuture, timeout)
      }
    }

    "throw a IllegalArgumentException if fired event is not a valid sensory event" in {
      val baker = setupBakerWithRecipe("NonExistingProcessEventTest")

      intercept[IllegalArgumentException] {
        baker.handleEvent(UUID.randomUUID().toString, SomeNotDefinedEvent("bla"))
      } should have('message("No event with name 'SomeNotDefinedEvent' found in the recipe"))
    }

    "execute an interaction when its ingredient is provided" in {
      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "only allow a sensory event be fired once if the max firing limit is set one" in {
      val recipe =
        Recipe("maxFiringLimitOfOneOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(1))

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      val executedFirst = baker.handleEvent(processId, InitialEvent(initialIngredientValue))
      executedFirst shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

      val executedSecond = baker.handleEvent(processId, InitialEvent(initialIngredientValue))
      executedSecond shouldBe SensoryEventStatus.FiringLimitMet
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
    }

    "only allow a sensory event be fired twice if the max firing limit is set two" in {
      val recipe =
        Recipe("maxFiringLimitOfTwoOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(2))

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      val executedFirst = baker.handleEvent(processId, InitialEvent(initialIngredientValue))
      executedFirst shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

      val executedSecond = baker.handleEvent(processId, InitialEvent(initialIngredientValue))
      executedSecond shouldBe SensoryEventStatus.Completed
      verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")

      // This check is added to verify event list is still correct after firing the same event twice
      baker.events(processId).map(_.name).toList shouldBe List("InitialEvent", "InteractionOneSuccessful", "InitialEvent", "InteractionOneSuccessful")

      val executedThird = baker.handleEvent(processId, InitialEvent(initialIngredientValue))
      executedThird shouldBe SensoryEventStatus.FiringLimitMet
      verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")
    }

    "backwards compatibility in serialization of case class ingredients" ignore {
      val tmpDir = System.getProperty("java.io.tmpdir")
      val journalPath = tmpDir + "/journal"
      val snapshotsPath = tmpDir + "/snapshots"
      val processId = "test-process-5"

      val actorSystem = ActorSystem("backwardsCompatibilityOfEvents", levelDbConfig("backwardsCompatibilityOfEvents", 3004, journalPath, snapshotsPath))
      val recoveryRecipeName = "backwardsCompatibilityOfEvents"

      try {
        val recipe =
          Recipe(recoveryRecipeName)
            .withInteraction(caseClassIngredientInteraction)
            .withInteraction(caseClassIngredientInteraction2)
            .withSensoryEvent(initialEvent)

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        val baker = new Baker(
          compiledRecipe = compiledRecipe,
          implementations = mockImplementations)(actorSystem)

        // Bake a new recipe, fire initial event. 2nd time baking with the same processId fails, so comment this part out after creating the process
        baker.bake(processId)

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

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      val processId = UUID.randomUUID().toString
      baker.bake(processId).toString

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testOptionalIngredientInteractionMock).apply(ingredientValue, Optional.empty(), Option.empty, Option.empty, initialIngredientValue)
      baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue)
    }

    "execute an interaction with Optionals boxed when its ingredient is provided as unboxed" in {

      val recipe =
        Recipe("IngredientProvidedRecipeWithUnboxedOptionals")
          .withInteraction(
            optionalIngredientInteraction)
          .withSensoryEvent(unboxedProviderEvent)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      val processId = UUID.randomUUID().toString
      baker.bake(processId).toString

      baker.handleEvent(processId, UnboxedProviderEvent(initialIngredientValue, initialIngredientValue, initialIngredientValue))

      verify(testOptionalIngredientInteractionMock).apply(java.util.Optional.of(initialIngredientValue), Optional.empty(), Some(initialIngredientValue), Option.empty, initialIngredientValue)
      baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue, "missingJavaOptional" -> initialIngredientValue, "missingScalaOptional" -> initialIngredientValue)
    }

    "notify a registered event listener of events" in {

      val listenerMock = mock[EventListener]

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val recipe =
        Recipe("EventListenerRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      baker.registerEventListener(listenerMock)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(listenerMock).processEvent(processId.toString, RuntimeEvent("InitialEvent", Seq("initialIngredient" -> initialIngredientValue)))
      verify(listenerMock).processEvent(processId.toString, RuntimeEvent("InteractionOneSuccessful", Seq("interactionOneOriginalIngredient" -> interactionOneIngredientValue)))
    }

    "execute an interaction when its ingredient is provided and the interaction is renamed" in {
      val recipe =
        Recipe("IngredientProvidedRecipeWithRename")
          .withInteraction(interactionOne, "interactionOneRenamed")
          .withSensoryEvent(initialEvent)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "execute an interaction when both ingredients are provided (join situation)" in {
      val baker = setupBakerWithRecipe("JoinRecipeForIngredients")

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)
      verify(testInteractionTwoMock).apply(initialIngredientValue)
      verify(testInteractionThreeMock).apply(interactionOneIngredientValue, interactionTwoIngredientValue)
      baker.getIngredients(processId) shouldBe afterInitialState
    }

    "execute an interaction when two events occur (join situation)" in {
      val baker = setupBakerWithRecipe("JoinRecipeForEvents")

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent("initialIngredient"))
      baker.handleEvent(processId, SecondEvent())

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock).apply("initialIngredient")
      verify(testInteractionThreeMock).apply("interactionOneIngredient",
        "interactionTwoIngredient")
      verify(testInteractionFourMock).apply()
      baker.getIngredients(processId) shouldBe finalState
    }

    "execute an interaction when one of the two events occur (OR situation)" in {
      val baker = {
        val recipe = Recipe("ORPreconditionedRecipeForEvents")
          .withInteractions(interactionFour
            .withRequiredOneOfEvents(initialEvent, secondEvent))
          .withSensoryEvents(initialEvent, secondEvent)

        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations)
      }

      val firstProcessId = UUID.randomUUID().toString
      baker.bake(firstProcessId)

      // Fire one of the events for the first process
      baker.handleEvent(firstProcessId, InitialEvent("initialIngredient"))
      verify(testInteractionFourMock).apply()

      // reset interaction mocks and fire the other event for the second process
      resetMocks

      val secondProcessId = UUID.randomUUID().toString
      baker.bake(secondProcessId)

      baker.handleEvent(secondProcessId, SecondEvent())
      verify(testInteractionFourMock).apply()
    }

    "execute two interactions which depend on same ingredient (fork situation)" in {

      val baker = setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent("initialIngredient"))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock).apply("initialIngredient")
    }

    "execute again after first execution completes and ingredient is produced again" in {

      val baker = setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent("initialIngredient"))

      verify(testInteractionOneMock, times(1)).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock, times(1)).apply("initialIngredient")

      baker.handleEvent(processId, InitialEvent("initialIngredient"))

      verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")
      verify(testInteractionTwoMock, times(2)).apply("initialIngredient")
    }

    "fire parallel transitions simultaneously" in {

      val baker = setupBakerWithRecipe("ParallelExecutionRecipe")

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

      baker.bake(processId)

      Thread.sleep(2000)

      val executingTimeInMilliseconds = timeBlockInMilliseconds {
        baker.handleEvent(processId, InitialEvent(initialIngredientValue))
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

      val baker = setupBakerWithRecipe("UpdateTestRecipe")

      val processId = UUID.randomUUID().toString

      when(testInteractionOneMock.apply(processId.toString, firstData)).thenReturn(firstResponse)
      when(testInteractionOneMock.apply(processId.toString, secondData)).thenReturn(secondResponse)

      baker.bake(processId)

      //Fire the first event
      baker.handleEvent(processId, InitialEvent(firstData))

      //Check that the first response returned
      baker.getIngredients(processId) shouldBe Map(
        "initialIngredient" -> firstData,
        "interactionOneIngredient" -> firstResponse,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue,
        "interactionThreeIngredient" -> interactionThreeIngredientValue
      )

      //Fire the second event
      baker.handleEvent(processId, InitialEvent(secondData))

      //Check that the second response is given
      baker.getIngredients(processId) shouldBe Map(
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

      val baker = new Baker(compiledRecipe = RecipeCompiler.compileRecipe(recipe), mockImplementations)
      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)

      val result = baker.getIngredients(processId)
      result shouldBe Map("initialIngredient" -> initialIngredientValue,
        "interactionOneIngredient" -> interactionOneIngredientValue)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verifyZeroInteractions(testInteractionOneMock)
    }

    "not throw an exception when an event is fired and a resulting interactions fails" in {
      val baker = setupBakerWithRecipe("FailingInteraction")
      when(testInteractionOneMock.apply(anyString, anyString()))
        .thenThrow(new RuntimeException(errorMessage))

      val processId = UUID.randomUUID().toString
      baker.bake(processId)
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))
    }

    "not crash when one process crashes but the other does not" in {

      val baker = setupBakerWithRecipe("CrashTestRecipe")

      val firstProcessId = UUID.randomUUID().toString
      val secondProcessId = UUID.randomUUID().toString
      when(testInteractionOneMock.apply(firstProcessId.toString, initialIngredientValue))
        .thenReturn(interactionOneIngredientValue)
      when(testInteractionOneMock.apply(secondProcessId.toString, initialIngredientValue))
        .thenThrow(new RuntimeException(errorMessage))
      baker.bake(firstProcessId)
      baker.bake(secondProcessId)

      // start the first process with firing an event
      baker.handleEvent(firstProcessId, InitialEvent(initialIngredientValue))

      // start the second process and expect a failure
      baker.handleEvent(secondProcessId, InitialEvent(initialIngredientValue))

      // fire another event for the first process
      baker.handleEvent(firstProcessId, SecondEvent())

      // expect first process state is correct
      baker.getIngredients(firstProcessId) shouldBe finalState
    }

    "keep the input data in accumulated state even if the interactions dependent on this event fail to execute" in {

      val baker = setupBakerWithRecipe("StatePersistentTestRecipe")
      val processId = UUID.randomUUID().toString
      when(testInteractionOneMock.apply(processId.toString, initialIngredientValue))
        .thenThrow(new RuntimeException(errorMessage))
      baker.bake(processId)

      // Send failing event and after that send succeeding event
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      val result = baker.getIngredients(processId)
      result shouldBe Map(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue)
    }

    "retry an interaction with incremental backoff if configured to do so" in {

      val baker = setupBakerWithRecipe("FailingInteractionWithBackof")
      when(testInteractionOneMock.apply(anyString(), anyString()))
        .thenThrow(new RuntimeException(errorMessage))

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      //Thread.sleep is needed since we need to wait for the expionental back of
      //100ms should be enough since it waits 20ms and then 40 ms
      Thread.sleep(200)
      //Since it can be called up to 3 times it should have been called 3 times in the 100ms
      verify(testInteractionOneMock, times(3)).apply(processId.toString, initialIngredientValue)
    }

    "not execute the failing interaction again each time after some other unrelated event is fired" in {

      /* This test FAILS because passportData FAIL_DATA is included in the marking while it should not! (?)
       * The fact that it is in the marking forces failingUploadPassport to fire again when second event fires!
       */
      val baker = setupBakerWithRecipe("ShouldNotReExecute")
      val processId = UUID.randomUUID().toString

      when(testInteractionTwoMock.apply(anyString())).thenThrow(new RuntimeException(errorMessage))
      baker.bake(processId)

      // first fired event causes a failure in the action
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))
      verify(testInteractionTwoMock, times(1)).apply(anyString())
      resetMocks

      // second fired, this should not re-execute InteractionOne and therefor not start InteractionThree
      baker.handleEvent(processId, SecondEvent())

      verify(testInteractionTwoMock, never()).apply(anyString())

      val result = baker.getIngredients(processId)
      result shouldBe Map(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionOneIngredient" -> interactionOneIngredientValue)
    }

    "fire the exhausted retry event if the max retry times for the interaction is met" in {

      val recipe = Recipe("FireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withIncrementalBackoffOnFailure(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          exhaustedRetryEvent = Some(exhaustedEvent)))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new BakerException())

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)(defaultActorSystem)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      //Handle first event
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      Thread.sleep(50)

      baker.events(processId).map(_.name) should contain (exhaustedEvent.name)
    }

    "not fire the exhausted retry event if the interaction passes" in {
      val recipe = Recipe("NotFireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withIncrementalBackoffOnFailure(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          exhaustedRetryEvent = Some(exhaustedEvent)))

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)(defaultActorSystem)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      //Handle first event
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      Thread.sleep(50)

      baker.events(processId).map(_.name) should not contain exhaustedEvent.name
    }

    "fire a specified failure event for an interaction immediately after it fails" in {

      val recipe = Recipe("ImmediateFailureEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(FireEventAfterFailure(exhaustedEvent)))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Some failure happened"))

      val baker = new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations)(defaultActorSystem)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      //Handle first event
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      Thread.sleep(50)

      baker.events(processId).map(_.name) should contain (exhaustedEvent.name)
    }

    "be able to return all occurred events" in {

      val baker = setupBakerWithRecipe("CheckEventRecipe")

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      //Handle first event
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      //Check if both the new event and the events occurred in the past are in the eventsList
      baker.events(processId) should contain only(
        RuntimeEvent("InitialEvent", Seq("initialIngredient" -> initialIngredientValue)),
        RuntimeEvent("SieveInteractionSuccessful", Seq("sievedIngredient" -> sievedIngredientValue)),
        RuntimeEvent("EventFromInteractionTwo", Seq("interactionTwoIngredient" -> interactionTwoIngredientValue)),
        RuntimeEvent("InteractionOneSuccessful", Seq("interactionOneIngredient" -> interactionOneIngredientValue)),
        RuntimeEvent("InteractionThreeSuccessful", Seq("interactionThreeIngredient" -> interactionThreeIngredientValue))
      )

      //Execute another event
      baker.handleEvent(processId, SecondEvent())

      //Check if both the new event and the events occurred in the past are in the eventsList
      baker.events(processId) should contain only(
        RuntimeEvent.apply("InitialEvent", Seq("initialIngredient" -> "initialIngredient")),
        RuntimeEvent.apply("EventFromInteractionTwo", Seq("interactionTwoIngredient" -> "interactionTwoIngredient")),
        RuntimeEvent.apply("SecondEvent", Seq.empty),
        RuntimeEvent.apply("InteractionOneSuccessful", Seq("interactionOneIngredient" -> interactionOneIngredientValue)),
        RuntimeEvent.apply("SieveInteractionSuccessful", Seq("sievedIngredient" -> sievedIngredientValue)),
        RuntimeEvent.apply("InteractionThreeSuccessful", Seq("interactionThreeIngredient" -> interactionThreeIngredientValue)),
        RuntimeEvent.apply("InteractionFourSuccessful", Seq("interactionFourIngredient" -> interactionFourIngredientValue))
      )
    }

    //Only works if persistence actors are used (think cassandra)
    "recover the state of a process from a persistence store" in {
      val system1 = ActorSystem("persistenceTest1", levelDbConfig("persistenceTest1", 3002))
      val recoveryRecipeName = "RecoveryRecipe"
      val processId = UUID.randomUUID().toString

      try {
        val baker1 = setupBakerWithRecipe(recoveryRecipeName, appendUUIDToTheRecipeName = false)(system1)

        baker1.bake(processId)
        baker1.handleEvent(processId, InitialEvent(initialIngredientValue))
        baker1.handleEvent(processId, SecondEvent())

        baker1.getIngredients(processId) shouldBe finalState
      } finally {
        TestKit.shutdownActorSystem(system1)
      }

      val system2 = ActorSystem("persistenceTest2", levelDbConfig("persistenceTest2", 3003))
      try {
        val baker2 = new Baker(compiledRecipe = RecipeCompiler.compileRecipe(getComplexRecipe(recoveryRecipeName)), mockImplementations)(system2)
        baker2.getIngredients(processId) shouldBe finalState
      } finally {
        TestKit.shutdownActorSystem(system2)
      }

    }

    "when acknowledging the first event, not wait on the rest" in {
      val baker = setupBakerWithRecipe("NotWaitForTheRest")

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
      baker.bake(processId)
      val response = baker.handleEventAsync(processId, InitialEvent(initialIngredientValue))

      import org.scalatest.concurrent.Timeouts._

      failAfter(Span(500, Milliseconds)) {
        Await.result(response.receivedFuture, 500 millis)
        response.completedFuture.isCompleted shouldEqual false
      }

      Await.result(response.completedFuture, 3000 millis)

      response.completedFuture.value should matchPattern { case Some(Success(_)) => }
    }

    "acknowledge the first and final event while rest processing failed" in {
      val baker = setupBakerWithRecipe("AcknowledgeThefirst")

      when(testInteractionTwoMock.apply(anyString()))
        .thenThrow(new RuntimeException("Unknown Exception."))

      val processId = UUID.randomUUID().toString
      baker.bake(processId)
      val response = baker.handleEventAsync(processId, InitialEvent(initialIngredientValue))
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
      val baker = setupBakerWithRecipe("OverlappingMultiIngredients")

      // It is helpful to check the recipe visualization if this test fails
      //      println(baker.compiledRecipe.getRecipeVisualization)

      val processId = UUID.randomUUID().toString
      baker.bake(processId)
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

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

      setupMockResponse()

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)(defaultActorSystem)


      val processId = UUID.randomUUID().toString
      baker.bake(processId)
      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

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

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)(defaultActorSystem)

      val processId = UUID.randomUUID().toString

      baker.bake(processId)

      Thread.sleep(receivePeriod.toMillis  + 100)

      baker.handleEvent(processId, InitialEvent("")) shouldBe SensoryEventStatus.ReceivePeriodExpired
    }

    "accept sensory events before a specified receive period" in {

      val receivePeriod: FiniteDuration = 10 seconds

      val recipe: Recipe =
        "eventReceiveInTimeRecipe"
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)(defaultActorSystem)

      val processId = UUID.randomUUID().toString

      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent("")) shouldBe SensoryEventStatus.Completed
    }

    "be able to visualize events that have been fired" in {
      //This test only checks if the graphviz is different, not that the outcome is correct
      val baker = setupBakerWithRecipe("CheckEventRecipe")

      val processId = UUID.randomUUID().toString
      baker.bake(processId)

      val noEventsGraph = baker.getVisualState(processId)
      //      System.out.println(noEventsGraph)

      //Handle first event
      baker.handleEvent(processId, InitialEvent("initialIngredient"))

      val firstEventGraph = baker.getVisualState(processId)
      //      System.out.println(firstEventGraph)

      noEventsGraph should not be firstEventGraph

      baker.handleEvent(processId, SecondEvent())
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

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)(defaultActorSystem)

      val processId = UUID.randomUUID().toString

      baker.bake(processId)

      baker.allProcessMetadata.map(_.id) should contain(processId)

      baker.getIngredients(processId)

      Thread.sleep(retentionPeriod.toMillis + 200)

      baker.allProcessMetadata.map(_.id) should not contain processId

      intercept[NoSuchProcessException] {
        baker.getIngredients(processId)
      }

      baker.events(processId) shouldBe empty
    }

    "block interaction and log error message if a null ingredient is provided directly by a Interaction" in {
      val recipe =
        Recipe("NullIngredientRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(null)

      val processId = UUID.randomUUID().toString

      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue)
    }

    "block interaction and log error message if a null ingredient is provided by an Event provided by a Interaction" in {
      val recipe =
        Recipe("NullIngredientFromEventRecipe")
          .withInteraction(interactionTwo
            .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"))
          .withSensoryEvent(initialEvent)

      val baker = new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations)

      when(testInteractionTwoMock.apply(anyString())).thenReturn(EventFromInteractionTwo(null))

      val processId = UUID.randomUUID().toString

      baker.bake(processId)

      baker.handleEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionTwoMock).apply("initialIngredient")
      baker.getIngredients(processId) shouldBe Map("initialIngredient" -> initialIngredientValue)
    }
  }
}
