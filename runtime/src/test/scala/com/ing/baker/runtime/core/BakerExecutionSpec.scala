package com.ing.baker.runtime.core

import java.util.concurrent.TimeUnit
import java.util.{Optional, UUID}

import akka.actor.ActorSystem
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.{TestDuration, TestKit, TestProbe}
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.types.Converters
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock
import org.mockito.stubbing.Answer
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.language.postfixOps

case class SomeNotDefinedEvent(name: String)

class BakerExecutionSpec extends BakerRuntimeTestBase {

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
        response.confirmReceived(timeout)
      }

      intercept[NoSuchProcessException] {
        response.confirmCompleted(timeout)
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

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      baker.getIngredients(processId) shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "Fire an event twice if two Interactions fire it both" in {

      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteractions(
            interactionTwo
              .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"),
            fireTwoEventsInteraction,
            interactionOne
              .withRequiredEvents(eventFromInteractionTwo))
          .withSensoryEvents(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

//      val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      println("recipe visualisation:")
//      println(baker.getCompiledRecipe(recipeId).getRecipeVisualization)
//      println("petrinet visualisation:")
//      println(baker.getCompiledRecipe(recipeId).getPetriNetVisualization)

      when(testInteractionTwoMock.apply(anyString()))
        .thenReturn(EventFromInteractionTwo("ingredient2"))
      when(testFireTwoEventsInteractionMock.apply(anyString()))
        .thenReturn(Event1FromInteractionSeven("ingredient3"))

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(testInteractionTwoMock).apply(initialIngredientValue)
      verify(testFireTwoEventsInteractionMock).apply(initialIngredientValue)
      verify(testInteractionOneMock).apply(processId, initialIngredientValue)
      baker.getProcessState(processId).eventNames should contain
        ("InitialEvent", "Event1FromInteractionSeven", "EventFromInteractionTwo", "InteractionOneSuccessful")
    }


    "only allow a sensory event be fired once if the max firing limit is set one" in {
      val recipe =
        Recipe("maxFiringLimitOfOneOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(1))

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

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

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

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

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

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

    "backwards compatibility in serialization of case class ingredients" in {

      import better.files._

      /**
        * This is the path where the original messages where persisted
        *
        * For the test they are copied to a temporary directory in /target
        *
        * !!! If you want to create a new test case the following flag to true
        */
      val createNewCase: Boolean = false

      val journalPath = "src/test/resources/persisted-messages"
      val journalDir = File(journalPath)

      val testPath = if (createNewCase) journalPath else "target/backwardsCompatibilityOfEvents"
      val testDir = File(testPath).createDirectoryIfNotExists()

      if (!createNewCase) {
        testDir.delete()
        testDir.createDirectory()
        journalDir./("journal").copyToDirectory(testDir)
      }

      val config = clusterLevelDBConfig(
        "backwardsCompatibilityOfEvents",
        3004,
        10 seconds,
        s"$testPath/journal",
        s"$testPath/snapshots")

      val actorSystem = ActorSystem("backwardsCompatibilityOfEvents", config)

      try {

        import com.ing.baker.Webshop._

        val recipe = Webshop.webshopRecipe

        // test data
        val customerInfo = new Webshop.CustomerInfo("klaas", "straat", "email")
        val processId = "backwards-compatible-process"
        val order = "123"
        val trackingId = "trackingId"
        val goods = "some goods"

        // mocks
        val shipGoodsMock: ShipGoods = mock[Webshop.ShipGoods]
        val sendInvoiceMock: SendInvoice = mock[Webshop.SendInvoice]
        val manufactureGoodsMock: ManufactureGoods = mock[Webshop.ManufactureGoods]
        val validateOrderMock: ValidateOrder = mock[Webshop.ValidateOrder]

        val implementations = Seq(shipGoodsMock, sendInvoiceMock, manufactureGoodsMock, validateOrderMock)

        val (baker, recipeId) = setupBakerWithRecipe(recipe, implementations)(actorSystem)

        def createProcess(): Unit = {

          baker.bake(recipeId, processId)

          // prepare mocks
          when(shipGoodsMock.apply(anyString(), any[CustomerInfo]())).thenReturn(new ShipGoods.GoodsShipped(trackingId))
          when(sendInvoiceMock.apply(any[CustomerInfo]())).thenReturn(new SendInvoice.InvoiceWasSent())
          when(manufactureGoodsMock.apply(anyString())).thenReturn(new ManufactureGoods.GoodsManufactured(goods))
          when(validateOrderMock.apply(anyString(), anyString())).thenReturn(new ValidateOrder.Valid())

          // process the events
          baker.processEvent(processId, new CustomerInfoReceived(customerInfo));
          baker.processEvent(processId, new OrderPlaced(order));
          baker.processEvent(processId, new PaymentMade());
        }

        if (createNewCase)
          createProcess();

        val expectedIngredients = ingredientMap(
          "customerInfo" -> customerInfo,
          "order" -> order,
          "goods" -> goods,
          "trackingId" -> trackingId)

        val expectedEvents = eventList(
          new CustomerInfoReceived(customerInfo),
          new OrderPlaced(order),
          new ValidateOrder.Valid(),
          new PaymentMade(),
          new ManufactureGoods.GoodsManufactured(goods),
          new ShipGoods.GoodsShipped(trackingId),
          new SendInvoice.InvoiceWasSent()
        )

        baker.getIngredients(processId) shouldBe expectedIngredients

        baker.events(processId) shouldBe expectedEvents

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

      baker.addImplementations(mockImplementations)

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

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

      val recipe =
        Recipe("EventListenerRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      baker.registerEventListener("EventListenerRecipe", listenerMock)

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))

      verify(listenerMock).processEvent(processId.toString, Baker.extractEvent(InitialEvent(initialIngredientValue)))
      verify(listenerMock).processEvent(processId.toString, Baker.extractEvent(InteractionOneSuccessful(interactionOneIngredientValue)))
    }

    "return a list of events that where caused by a sensory event" in {

      val (baker, recipeId) = setupBakerWithRecipe("SensoryEventDeltaRecipe")

      val processId = UUID.randomUUID().toString

      baker.bake(recipeId, processId)

      val response = baker.processEventAsync(processId, InitialEvent(initialIngredientValue))

      response.confirmReceived() shouldBe SensoryEventStatus.Received
      response.confirmCompleted() shouldBe SensoryEventStatus.Completed

      response.confirmAllEvents(timeout) should contain only (
         RuntimeEvent("InitialEvent", Seq(initialIngredient("initialIngredient"))),
         RuntimeEvent("SieveInteractionSuccessful", Seq(sievedIngredient("sievedIngredient"))),
         RuntimeEvent("InteractionOneSuccessful", Seq(interactionOneIngredient("interactionOneIngredient"))),
         RuntimeEvent("EventFromInteractionTwo", Seq(interactionTwoIngredient("interactionTwoIngredient"))),
         RuntimeEvent("InteractionThreeSuccessful", Seq(interactionThreeIngredient("interactionThreeIngredient")))
      )
    }

    "execute an interaction when its ingredient is provided and the interaction is renamed" in {
      val recipe =
        Recipe("IngredientProvidedRecipeWithRename")
          .withInteraction(interactionOne.withName("interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

      val (baker, recipeId) = setupBakerWithRecipe(recipe, mockImplementations)

      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

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
      when(testInteractionOneMock.apply(anyString(), anyString())).thenAnswer(new Answer[InteractionOneSuccessful] {
        override def answer(invocationOnMock: InvocationOnMock): InteractionOneSuccessful = {
          Thread.sleep(500)
          InteractionOneSuccessful(interactionOneIngredientValue)
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
        s"If it takes less than 1 second to execute we can be sure the two actions have executed in parallel. " +
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

      when(testInteractionOneMock.apply(processId.toString, firstData)).thenReturn(InteractionOneSuccessful(firstResponse))
      when(testInteractionOneMock.apply(processId.toString, secondData)).thenReturn(InteractionOneSuccessful(secondResponse))

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
            .withEventOutputTransformer(interactionOneSuccessful, Map("interactionOneOriginalIngredient" -> "interactionOneIngredient"))
            .withMaximumInteractionCount(1))
        .withSensoryEvent(initialEvent)

      when(testInteractionOneMock.apply(anyString(), anyString()))
        .thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))

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
        .thenReturn(InteractionOneSuccessful(interactionOneIngredientValue))
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
      verify(listenerMock).processEvent(processId.toString, Baker.extractEvent(InitialEvent(initialIngredientValue)))
      verify(listenerMock).processEvent(processId.toString, RuntimeEvent(interactionOne.retryExhaustedEventName, Seq.empty))

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
        Baker.extractEvent(InitialEvent(initialIngredientValue)),
        Baker.extractEvent(SieveInteractionSuccessful(sievedIngredientValue)),
        Baker.extractEvent(EventFromInteractionTwo(interactionTwoIngredientValue)),
        RuntimeEvent("InteractionOneSuccessful", Seq("interactionOneIngredient" -> Converters.toValue(interactionOneIngredientValue))),
        Baker.extractEvent(InteractionThreeSuccessful(interactionThreeIngredientValue))
      )

      //Execute another event
      baker.processEvent(processId, SecondEvent())

      //Check if both the new event and the events occurred in the past are in the eventsList
      baker.events(processId) should contain only(
        Baker.extractEvent(InitialEvent(initialIngredientValue)),
        Baker.extractEvent(EventFromInteractionTwo(interactionTwoIngredientValue)),
        RuntimeEvent("SecondEvent", Seq.empty),
        RuntimeEvent("InteractionOneSuccessful", Seq("interactionOneIngredient" -> Converters.toValue(interactionOneIngredientValue))),
        Baker.extractEvent(SieveInteractionSuccessful(sievedIngredientValue)),
        Baker.extractEvent(InteractionThreeSuccessful(interactionThreeIngredientValue)),
        Baker.extractEvent(InteractionFourSuccessful(interactionFourIngredientValue))
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

    "be able to return an index of all processes in cluster mode" in {

      val journalId = java.util.UUID.randomUUID().toString

      val indexTestSystem = ActorSystem("indexTest", clusterLevelDBConfig(
        actorSystemName = "indexTest",
        port = 3005,
        journalPath = s"target/journal-$journalId",
        snapshotsPath = s"target/snapshots-$journalId"))

      val nrOfProcesses = 200

      try {
        val (baker, recipeId) = setupBakerWithRecipe("IndexTestCluster")(indexTestSystem)

        val processIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet

        processIds.foreach(id => baker.bake(recipeId, id))

        baker.getIndex().map(_.processId) shouldBe processIds
      }
      finally {
        TestKit.shutdownActorSystem(indexTestSystem)
      }
    }

    "be able to return an index of all processes in local/inmemory mode" in {

      val nrOfProcesses = 200

      val (baker, recipeId) = setupBakerWithRecipe("IndexTestLocal")

      val processIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet

      processIds.foreach(id => baker.bake(recipeId, id))

      baker.getIndex().map(_.processId) shouldBe processIds
    }

    //Only works if persistence actors are used (think cassandra)
    "recover the state of a process from a persistence store" in {
      val system1 = ActorSystem("persistenceTest1", localLevelDBConfig("persistenceTest1"))
      val recoveryRecipeName = "RecoveryRecipe"
      val processId = UUID.randomUUID().toString

      var recipeId: String = ""
      val compiledRecipe = RecipeCompiler.compileRecipe(getRecipe(recoveryRecipeName))

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

      val system2 = ActorSystem("persistenceTest2", localLevelDBConfig("persistenceTest2"))
      try {
        val baker2 = new Baker()(system2)
        baker2.addImplementations(mockImplementations)
        baker2.getIngredients(processId) shouldBe finalState
        baker2.getRecipe(recipeId).compiledRecipe shouldBe compiledRecipe
        baker2.addRecipe(compiledRecipe) shouldBe recipeId
      } finally {
        TestKit.shutdownActorSystem(system2)
      }
    }

    "when acknowledging the first event, not wait on the rest" in {
      val (baker, recipeId) = setupBakerWithRecipe("NotWaitForTheRest")

      val interaction2Delay = 2000

      when(testInteractionTwoMock.apply(anyString())).thenAnswer {
        //Do not remove next line, still needed in 2.11
        new Answer[EventFromInteractionTwo] {
          override def answer(invocation: InvocationOnMock): EventFromInteractionTwo = {
            Thread.sleep(interaction2Delay)
            interactionTwoEventValue
          }
        }
      }

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      val response: BakerResponse = baker.processEventAsync(processId, InitialEvent(initialIngredientValue))

      response.confirmCompleted(3000 millis) shouldBe SensoryEventStatus.Completed
    }

    "acknowledge the first and final event while rest processing failed" in {
      val (baker, recipeId) = setupBakerWithRecipe("AcknowledgeThefirst")

      when(testInteractionTwoMock.apply(anyString()))
        .thenThrow(new RuntimeException("Unknown Exception.")) // This interaction is not retried and blocks the process

      val processId = UUID.randomUUID().toString
      baker.bake(recipeId, processId)
      val response = baker.processEventAsync(processId, InitialEvent(initialIngredientValue))

      response.confirmReceived() shouldBe SensoryEventStatus.Received

      // The process is completed because it is in a BLOCKED state
      response.confirmCompleted(3 seconds) shouldBe SensoryEventStatus.Completed
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
        Recipe("sameIngredientMultipleTime")
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
        Recipe("eventReceiveExpirationRecipe")
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
        Recipe("eventReceiveInTimeRecipe")
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
        Recipe("RetentionPeriodRecipe")
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
