package com.ing.baker.runtime.akka

import java.util.concurrent.TimeUnit
import java.util.{Optional, UUID}

import akka.actor.ActorSystem
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.stream.ActorMaterializer
import akka.testkit.{TestDuration, TestKit, TestProbe}
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.BakerException._
import com.ing.baker.runtime.common._
import com.ing.baker.runtime.scaladsl.{Baker, RuntimeEvent, InteractionImplementation}
import com.typesafe.config.ConfigFactory
import org.mockito.Matchers.{eq => mockitoEq, _}
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock
import org.mockito.stubbing.Answer
import org.slf4j.LoggerFactory

import scala.concurrent.Future
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
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FirstTimeBaking")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
      } yield succeed
    }

    "throw an IllegalArgumentException if a baking a process with the same identifier twice" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("DuplicateIdentifierRecipe")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- recoverToSucceededIf[IllegalArgumentException] {
          baker.bake(recipeId, id)
        }
      } yield succeed
    }

    "throw a NoSuchProcessException when requesting the process state of a non existing process" in {
      for {
        (baker, _) <- setupBakerWithRecipe("NonExistingProcessTest")
        _ <- recoverToSucceededIf[NoSuchProcessException] {
          baker.getProcessState(UUID.randomUUID().toString)
        }
      } yield succeed
    }

    "throw a NoSuchProcessException when attempting to fire an event for a non existing process" in {
      for {
        (baker, _) <- setupBakerWithRecipe("NonExistingProcessEventTest")
        event = RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient"))
        response = baker.fireSensoryEvent(UUID.randomUUID().toString, event)
        _ <- recoverToSucceededIf[NoSuchProcessException] {
          response.received
        }
        _ <- recoverToSucceededIf[NoSuchProcessException] {
          response.completed
        }
      } yield succeed
    }

    "throw a IllegalArgumentException if fired event is not a valid sensory event" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("NonExistingProcessEventTest")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        intercepted <- recoverToExceptionIf[IllegalArgumentException] {
          baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(SomeNotDefinedEvent("bla")))
        }
        _ = intercepted.getMessage should startWith("No event with name 'SomeNotDefinedEvent' found in recipe 'NonExistingProcessEventTest")
      } yield succeed
    }

    "execute an interaction when its ingredient is provided" in {
      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
        state <- baker.getProcessState(processId)
      } yield
        state.ingredients shouldBe
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

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionTwoMock.apply(anyString()))
          .thenReturn(EventFromInteractionTwo("ingredient2"))
        _ = when(testFireTwoEventsInteractionMock.apply(anyString()))
          .thenReturn(Event1FromInteractionSeven("ingredient3"))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionTwoMock).apply(initialIngredientValue)
        _ = verify(testFireTwoEventsInteractionMock).apply(initialIngredientValue)
        _ = verify(testInteractionOneMock).apply(processId, initialIngredientValue)
        state <- baker.getProcessState(processId)
      } yield state.eventNames should contain allOf("InitialEvent", "Event1FromInteractionSeven", "EventFromInteractionTwo", "InteractionOneSuccessful")
    }

    "only allow a sensory event be fired once if the max firing limit is set one" in {
      val recipe =
        Recipe("maxFiringLimitOfOneOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(1))

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)

        response0 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response0.status shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

        response1 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response1.status shouldBe SensoryEventStatus.FiringLimitMet
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
      } yield succeed
    }

    "not allow a sensory event be fired twice with the same correlation id" in {
      val recipe =
        Recipe("correlationIdSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)

        response0 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)), "abc")
        _ = response0.status shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

        response1 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)), "abc")
        _ = response1.status shouldBe SensoryEventStatus.AlreadyReceived
        _ = verifyNoMoreInteractions(testInteractionOneMock)
      } yield succeed
    }

    "only allow a sensory event be fired twice if the max firing limit is set two" in {
      val recipe =
        Recipe("maxFiringLimitOfTwoOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(2))

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)

        response0 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response0.status shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")

        response1 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response1.status shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")

        // This check is added to verify event list is still correct after firing the same event twice
        state <- baker.getProcessState(processId)
        _ = state.eventNames shouldBe List("InitialEvent", "InteractionOneSuccessful", "InitialEvent", "InteractionOneSuccessful")

        response2 <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response2.status shouldBe SensoryEventStatus.FiringLimitMet
        _ = verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")
      } yield succeed
    }

    "backwards compatibility in serialization of case class ingredients, THIS TEST IS BROKEN FIX ME!" ignore {

      val isWindows: Boolean = System.getProperty("os.name").toLowerCase.contains("windows")

      // This tests are broken on windows, requires some investigation
      // Still broken, cause unknown, might be that we stopped being backwards compatible or data got corrupted
      if (isWindows) Future.successful {
        println(Console.YELLOW + "WARNING: You are testing on a Windows system, notice that this test is not working and needs to eventually be addressed")
        succeed
      } else {
        import better.files._

        /**
          * This is the path where the original messages where persisted
          *
          * For the test they are copied to a temporary directory in /target
          *
          * !!! If you want to create a new test case the following flag to true
          */
        val createNewCase: Boolean = false

        val journalPath = "src/test/resources/persisted-messages" + (if (isWindows) "-windows" else "")
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
        val materializer = ActorMaterializer.create(actorSystem)

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

        val implementations = Seq(shipGoodsMock, sendInvoiceMock, manufactureGoodsMock, validateOrderMock).map(InteractionImplementation.unsafeFrom(_))

        def createProcess(baker: Baker, recipeId: String): Future[Unit] = {
          for {
            _ <- baker.bake(recipeId, processId)
            // prepare mocks
            _ = when(shipGoodsMock.apply(anyString(), any[CustomerInfo]())).thenReturn(new ShipGoods.GoodsShipped(trackingId))
            _ = when(sendInvoiceMock.apply(any[CustomerInfo]())).thenReturn(new SendInvoice.InvoiceWasSent())
            _ = when(manufactureGoodsMock.apply(anyString())).thenReturn(new ManufactureGoods.GoodsManufactured(goods))
            _ = when(validateOrderMock.apply(anyString(), anyString())).thenReturn(new ValidateOrder.Valid())

            // process the events
            _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(new CustomerInfoReceived(customerInfo)))
            _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(new OrderPlaced(order)))
            _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(new PaymentMade()))
          } yield ()
        }

        (for {
          (baker, recipeId) <- setupBakerWithRecipe(recipe, implementations)(actorSystem, materializer)
          _ <- if (createNewCase) createProcess(baker, recipeId) else Future.unit

          expectedIngredients = ingredientMap(
            "customerInfo" -> customerInfo,
            "order" -> order,
            "goods" -> goods,
            "trackingId" -> trackingId)

          expectedEvents = eventList(
            new CustomerInfoReceived(customerInfo),
            new OrderPlaced(order),
            new ValidateOrder.Valid(),
            new PaymentMade(),
            new ManufactureGoods.GoodsManufactured(goods),
            new ShipGoods.GoodsShipped(trackingId),
            new SendInvoice.InvoiceWasSent()
          )

          state <- baker.getProcessState(processId)
          _ = state.ingredients shouldBe expectedIngredients
          _ = state.eventNames shouldBe expectedEvents.map(_.name)
        } yield succeed).transform(
          { e => TestKit.shutdownActorSystem(actorSystem); e },
          { a => TestKit.shutdownActorSystem(actorSystem); a }
        )
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

      val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

      for {
        _ <- baker.addImplementations(mockImplementations)

        compiledRecipe = RecipeCompiler.compileRecipe(recipe)
        recipeId <- baker.addRecipe(compiledRecipe)

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)

        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testOptionalIngredientInteractionMock).apply(ingredientValue, Optional.empty(), Option.empty, Option.empty, initialIngredientValue)
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
    }

    "execute an interaction with Optionals boxed when its ingredient is provided as unboxed" in {
      val recipe =
        Recipe("IngredientProvidedRecipeWithUnboxedOptionals")
          .withInteraction(
            optionalIngredientInteraction)
          .withSensoryEvent(unboxedProviderEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)

        processId = UUID.randomUUID().toString

        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(UnboxedProviderEvent(initialIngredientValue, initialIngredientValue, initialIngredientValue)))

        _ = verify(testOptionalIngredientInteractionMock).apply(java.util.Optional.of(initialIngredientValue), Optional.empty(), Some(initialIngredientValue), Option.empty, initialIngredientValue)
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "missingJavaOptional" -> initialIngredientValue, "missingScalaOptional" -> initialIngredientValue)
    }

    "notify a registered event listener of events" in {
      val listenerMock = mock[EventListener]
      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
      val recipe =
        Recipe("EventListenerRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ <- baker.registerEventListener("EventListenerRecipe", listenerMock)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(listenerMock).processEvent(mockitoEq(processId.toString), argThat(new RuntimeEventMatcher(RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))))
        _ = verify(listenerMock).processEvent(mockitoEq(processId.toString), argThat(new RuntimeEventMatcher(RuntimeEvent.unsafeFrom(InteractionOneSuccessful(interactionOneIngredientValue)))))
      } yield succeed
    }

    "return a list of events that where caused by a sensory event" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("SensoryEventDeltaRecipe")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        response = baker.fireSensoryEvent(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        confirmReceived <- response.received
        _ = confirmReceived shouldBe SensoryEventStatus.Received
        confirmCompleted <- response.completed
        _ = confirmCompleted.status shouldBe SensoryEventStatus.Completed
        _ = confirmCompleted.ingredients.keys should contain only(
          "initialIngredient",
          "sievedIngredient",
          "interactionOneIngredient",
          "interactionTwoIngredient",
          "interactionThreeIngredient"
        )
      } yield confirmCompleted.events should contain only(
        "InitialEvent",
        "SieveInteractionSuccessful",
        "InteractionOneSuccessful",
        "EventFromInteractionTwo",
        "InteractionThreeSuccessful"
      )
    }

    "execute an interaction when its ingredient is provided and the interaction is renamed" in {
      val recipe =
        Recipe("IngredientProvidedRecipeWithRename")
          .withInteraction(interactionOne.withName("interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "execute an interaction when both ingredients are provided (join situation)" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("JoinRecipeForIngredients")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)
        _ = verify(testInteractionTwoMock).apply(initialIngredientValue)
        _ = verify(testInteractionThreeMock).apply(interactionOneIngredientValue, interactionTwoIngredientValue)
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe afterInitialState
    }

    "execute an interaction when two events occur (join situation)" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("JoinRecipeForEvents")

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)

        response0 = baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        response1 = baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(SecondEvent()))
        _ <- response0
        _ <- response1

        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock).apply("initialIngredient")
        _ = verify(testInteractionThreeMock).apply("interactionOneIngredient",
          "interactionTwoIngredient")
        _ = verify(testInteractionFourMock).apply()
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe finalState
    }

    "execute an interaction when one of the two events occur (OR situation)" in {
      val recipe = Recipe("ORPreconditionedRecipeForEvents")
        .withInteractions(interactionFour
          .withRequiredOneOfEvents(initialEvent, secondEvent))
        .withSensoryEvents(initialEvent, secondEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        firstProcessId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, firstProcessId)
        // Fire one of the events for the first process
        _ <- baker.fireSensoryEventCompleted(firstProcessId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionFourMock).apply()
        // reset interaction mocks and fire the other event for the second process
        _ = resetMocks()
        secondProcessId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, secondProcessId)
        _ <- baker.fireSensoryEventCompleted(secondProcessId, RuntimeEvent.unsafeFrom(SecondEvent()))
        _ = verify(testInteractionFourMock).apply()
      } yield succeed
    }

    "execute an interaction when one of the two events occur with two or conditions (OR situation 2)" in {
      val recipe = Recipe("ORPreconditionedRecipeForEvents2")
        .withInteractions(interactionFour
          .withRequiredOneOfEvents(initialEvent, secondEvent)
          .withRequiredOneOfEvents(thirdEvent, fourthEvent))
        .withSensoryEvents(initialEvent, secondEvent, thirdEvent, fourthEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        firstProcessId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, firstProcessId)
        // Fire one of the events for the first process
        _ <- baker.fireSensoryEventCompleted(firstProcessId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionFourMock, times(0)).apply()
        _ <- baker.fireSensoryEventCompleted(firstProcessId, RuntimeEvent.unsafeFrom(ThirdEvent()))
        _ = verify(testInteractionFourMock).apply()
      } yield succeed
    }

    "execute two interactions which depend on same ingredient (fork situation)" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionOneMock).apply(processId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock).apply("initialIngredient")
      } yield succeed
    }

    "execute again after first execution completes and ingredient is produced again" in {

      for {
        (baker, recipeId) <- setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionOneMock, times(1)).apply(processId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock, times(1)).apply("initialIngredient")
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionOneMock, times(2)).apply(processId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock, times(2)).apply("initialIngredient")
      } yield succeed
    }

    "fire parallel transitions simultaneously" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("ParallelExecutionRecipe")
        // Two answers that take 0.6 seconds each!
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenAnswer((_: InvocationOnMock) => {
          Future {
            Thread.sleep(600)
            InteractionOneSuccessful(interactionOneIngredientValue)
          }(defaultActorSystem.dispatcher)
        })
        _ = when(testInteractionTwoMock.apply(anyString()))
          .thenAnswer((_: InvocationOnMock) => {
            Thread.sleep(600)
            EventFromInteractionTwo(interactionTwoIngredientValue)
          })
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        start = System.currentTimeMillis()
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        finish = System.currentTimeMillis()
        executingTimeInMilliseconds = finish - start
      } yield
        assert(
          executingTimeInMilliseconds < 1000,
          s"If it takes less than 1 second to execute we can be sure the two actions have executed in parallel. " +
            s"The execution took: $executingTimeInMilliseconds milliseconds and have executed sequentially...")
    }

    "update the state with new data if an event occurs twice" in {

      val firstData: String = "firstData"
      val secondData: String = "secondData"
      val firstResponse = "firstResponse"
      val secondResponse = "secondResponse"

      for {
        (baker, recipeId) <- setupBakerWithRecipe("UpdateTestRecipe")
        processId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(processId.toString, firstData)).thenReturn(Future.successful(InteractionOneSuccessful(firstResponse)))
        _ = when(testInteractionOneMock.apply(processId.toString, secondData)).thenReturn(Future.successful(InteractionOneSuccessful(secondResponse)))
        _ <- baker.bake(recipeId, processId)
        //Fire the first event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(firstData)))
        state0 <- baker.getProcessState(processId)
        //Check that the first response returned
        _ = state0.ingredients shouldBe ingredientMap(
          "initialIngredient" -> firstData,
          "interactionOneIngredient" -> firstResponse,
          "sievedIngredient" -> sievedIngredientValue,
          "interactionTwoIngredient" -> interactionTwoIngredientValue,
          "interactionThreeIngredient" -> interactionThreeIngredientValue
        )
        //Fire the second event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(secondData)))
        //Check that the second response is given
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe ingredientMap(
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
        .thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)
        state <- baker.getProcessState(processId)
        _ = state.ingredients shouldBe ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneIngredient" -> interactionOneIngredientValue)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verifyZeroInteractions(testInteractionOneMock)
      } yield succeed
    }

    "not throw an exception when an event is fired and a resulting interactions fails" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FailingInteraction")
        _ = when(testInteractionOneMock.apply(anyString, anyString()))
          .thenThrow(new RuntimeException(errorMessage))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield succeed
    }

    "not crash when one process crashes but the other does not" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CrashTestRecipe")

        firstProcessId = UUID.randomUUID().toString
        secondProcessId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(firstProcessId.toString, initialIngredientValue))
          .thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
        _ = when(testInteractionOneMock.apply(secondProcessId.toString, initialIngredientValue))
          .thenThrow(new RuntimeException(errorMessage))
        _ <- baker.bake(recipeId, firstProcessId)
        _ <- baker.bake(recipeId, secondProcessId)
        // start the first process with firing an event
        _ <- baker.fireSensoryEventCompleted(firstProcessId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        // start the second process and expect a failure
        _ <- baker.fireSensoryEventCompleted(secondProcessId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        // fire another event for the first process
        _ <- baker.fireSensoryEventCompleted(firstProcessId, RuntimeEvent.unsafeFrom(SecondEvent()))
        // expect first process state is correct
        state <- baker.getProcessState(firstProcessId)
      } yield state.ingredients shouldBe finalState
    }

    "keep the input data in accumulated state even if the interactions dependent on this event fail to execute" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("StatePersistentTestRecipe")
        processId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(processId.toString, initialIngredientValue))
          .thenThrow(new RuntimeException(errorMessage))
        _ <- baker.bake(recipeId, processId)

        // Send failing event and after that send succeeding event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe ingredientMap(
        "initialIngredient" -> initialIngredientValue,
        "sievedIngredient" -> sievedIngredientValue,
        "interactionTwoIngredient" -> interactionTwoIngredientValue)
    }

    "retry an interaction with incremental backoff if configured to do so" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FailingInteractionWithBackof")
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException(errorMessage))

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))

        //Thread.sleep is needed since we need to wait for the expionental back of
        //100ms should be enough since it waits 20ms and then 40 ms
        _ <- Future {
          Thread.sleep(200)
        }
        //Since it can be called up to 3 times it should have been called 3 times in the 100ms
        _ = verify(testInteractionOneMock, times(4)).apply(processId.toString, initialIngredientValue)
      } yield succeed
    }

    "not execute the failing interaction again each time after some other unrelated event is fired" in {
      /* This test FAILS because passportData FAIL_DATA is included in the marking while it should not! (?)
       * The fact that it is in the marking forces failingUploadPassport to fire again when second event fires!
       */
      for {
        (baker, recipeId) <- setupBakerWithRecipe("ShouldNotReExecute")
        processId = UUID.randomUUID().toString

        _ = when(testInteractionTwoMock.apply(anyString())).thenThrow(new RuntimeException(errorMessage))
        _ <- baker.bake(recipeId, processId)

        // first fired event causes a failure in the action
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionTwoMock, times(1)).apply(anyString())
        _ = resetMocks()

        // second fired, this should not re-execute InteractionOne and therefor not start InteractionThree
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(SecondEvent()))
        _ = verify(testInteractionTwoMock, never()).apply(anyString())
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe ingredientMap(
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

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new IllegalStateException())

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        //Handle first event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- Future {
          Thread.sleep(50)
        }
        state <- baker.getProcessState(processId)
      } yield state.eventNames should contain(interactionOne.retryExhaustedEventName)
    }

    "not fire the exhausted retry event if the interaction passes" in {
      val recipe = Recipe("NotFireExhaustedEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
          initialDelay = 10 milliseconds,
          maximumRetries = 1,
          fireRetryExhaustedEvent = Some(None))))

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        //Handle first event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- Future {
          Thread.sleep(50)
        }
        //Since the defaultEventExhaustedName is set the retryExhaustedEventName of interactionOne will be picked.
        state <- baker.getProcessState(processId)
      } yield state.eventNames should not contain interactionOne.retryExhaustedEventName
    }

    "fire a specified failure event for an interaction immediately after it fails" in {

      val recipe = Recipe("ImmediateFailureEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(FireEventAfterFailure()))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Some failure happened"))

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)

        listenerMock = mock[EventListener]
        _ <- baker.registerEventListener("ImmediateFailureEvent", listenerMock)

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)

        //Handle first event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- Future {
          Thread.sleep(50)
        }
        _ = verify(listenerMock).processEvent(mockitoEq(processId.toString), argThat(new RuntimeEventMatcher(RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))))
        _ = verify(listenerMock).processEvent(mockitoEq(processId.toString), argThat(new RuntimeEventMatcher(RuntimeEvent(interactionOne.retryExhaustedEventName, Map.empty))))

        state <- baker.getProcessState(processId)
      } yield state.eventNames should contain(interactionOne.retryExhaustedEventName)
    }

    "resolve a blocked interaction" in {
      val recipe =
        Recipe("ResolveBlockedInteractionRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Expected test failure"))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        state0 <- baker.getProcessState(processId)
        _ = state0.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue)
        _ <- baker.resolveInteraction(processId, interactionOne.name, RuntimeEvent.unsafeFrom(InteractionOneSuccessful("success!")))
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> "success!")
    }

    "retry a blocked interaction" in {
      val recipe =
        Recipe("RetryBlockedInteractionRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException("Expected test failure"))
          .thenReturn(Future.successful(InteractionOneSuccessful("success!")))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        state0 <- baker.getProcessState(processId)
        _ = state0.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue)
        _ <- baker.retryInteraction(processId, interactionOne.name)
        state <- baker.getProcessState(processId)
      } yield state.ingredients shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> "success!")
    }

    "be able to return all occurred events" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        //Handle first event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        //Check if both the new event and the events occurred in the past are in the eventsList
        state0 <- baker.getProcessState(processId)
        _ = state0.eventNames should contain only(
          "InitialEvent",
          "SieveInteractionSuccessful",
          "EventFromInteractionTwo",
          "InteractionOneSuccessful",
          "InteractionThreeSuccessful"
        )
        //Execute another event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(SecondEvent()))
        //Check if both the new event and the events occurred in the past are in the eventsList
        state <- baker.getProcessState(processId)
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

    "be able to return an index of all processes in cluster mode" in {
      val journalId = java.util.UUID.randomUUID().toString
      val indexTestSystem = ActorSystem("indexTest", clusterLevelDBConfig(
        actorSystemName = "indexTest",
        port = 3005,
        journalPath = s"target/journal-$journalId",
        snapshotsPath = s"target/snapshots-$journalId"))
      val materializer = ActorMaterializer.create(indexTestSystem)
      val nrOfProcesses = 200

      for {
        (baker, recipeId) <- setupBakerWithRecipe("IndexTestCluster")(indexTestSystem, materializer)
        processIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
        _ <- Future.traverse(processIds)(baker.bake(recipeId, _))
        index <- baker.getIndex
      } yield index.map(_.processId) shouldBe processIds
    }

    "be able to return an index of all processes in local/inmemory mode" in {

      val nrOfProcesses = 200

      for {
        (baker, recipeId) <- setupBakerWithRecipe("IndexTestLocal")
        processIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
        _ <- Future.traverse(processIds)(baker.bake(recipeId, _))
        index <- baker.getIndex
      } yield index.map(_.processId) shouldBe processIds
    }

    //Only works if persistence actors are used (think cassandra)
    "recover the state of a process from a persistence store" in {
      val system1 = ActorSystem("persistenceTest1", localLevelDBConfig("persistenceTest1"))
      val mat1 = ActorMaterializer.create(system1)
      val recoveryRecipeName = "RecoveryRecipe"
      val processId = UUID.randomUUID().toString

      val compiledRecipe = RecipeCompiler.compileRecipe(getRecipe(recoveryRecipeName))

      val first = (for {
        baker1 <- setupBakerWithNoRecipe()(system1, mat1)
        recipeId <- baker1.addRecipe(compiledRecipe)
        _ <- baker1.bake(recipeId, processId)
        _ <- baker1.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- baker1.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(SecondEvent()))
        state <- baker1.getProcessState(processId)
        _ = state.ingredients shouldBe finalState
      } yield recipeId).transform(
        { a => TestKit.shutdownActorSystem(system1); a },
        { a => TestKit.shutdownActorSystem(system1); a }
      )

      def second(recipeId: String) = {
        val system2 = ActorSystem("persistenceTest2", localLevelDBConfig("persistenceTest2"))
        val mat2 = ActorMaterializer.create(system2)
        val baker2 = Baker.akka(ConfigFactory.load(), system2, mat2)
        (for {
          _ <- baker2.addImplementations(mockImplementations)
          state <- baker2.getProcessState(processId)
          recipe <- baker2.getRecipe(recipeId)
          recipeId0 <- baker2.addRecipe(compiledRecipe)
        } yield {
          state.ingredients shouldBe finalState
          recipe.compiledRecipe shouldBe compiledRecipe
          recipeId0 shouldBe recipeId
        }).transform(
          { a => TestKit.shutdownActorSystem(system2); a },
          { a => TestKit.shutdownActorSystem(system2); a }
        )
      }

      first.flatMap(second)
    }

    "when acknowledging the first event, not wait on the rest" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("NotWaitForTheRest")
        interaction2Delay = 2000
        _ = when(testInteractionTwoMock.apply(anyString())).thenAnswer {
          //Do not remove next line, still needed in 2.11
          new Answer[EventFromInteractionTwo] {
            override def answer(invocation: InvocationOnMock): EventFromInteractionTwo = {
              Thread.sleep(interaction2Delay)
              interactionTwoEventValue
            }
          }
        }
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        completed <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield completed.status shouldBe SensoryEventStatus.Completed
    }

    "acknowledge the first and final event while rest processing failed" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("AcknowledgeThefirst")
        _ = when(testInteractionTwoMock.apply(anyString()))
          .thenThrow(new RuntimeException("Unknown Exception.")) // This interaction is not retried and blocks the process
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        response = baker.fireSensoryEvent(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        received <- response.received
        _ = received shouldBe SensoryEventStatus.Received
        completed <- response.completed
        // The process is completed because it is in a BLOCKED state
        _ = completed.status shouldBe SensoryEventStatus.Completed
      } yield succeed
    }

    "bind multi transitions correctly even if ingredient name overlaps" in {
      //This test is part of the ExecutionSpec and not the Compiler spec because the only correct way to validate
      //for this test is to check if Baker calls the mocks.
      //If there is a easy way to validate the created petrinet by the compiler it should be moved to the compiler spec.
      for {
        (baker, recipeId) <- setupBakerWithRecipe("OverlappingMultiIngredients")

        // It is helpful to check the recipe visualization if this test fails
        //      println(baker.compiledRecipe.getRecipeVisualization)

        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testInteractionOneMock, times(1)).apply(processId.toString, initialIngredientValue)
        _ = verify(testInteractionTwoMock, times(1)).apply(initialIngredientValue)
        _ = verifyNoMoreInteractions(testInteractionFiveMock, testInteractionSixMock)
      } yield succeed
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

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString

        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testInteractionOneMock, times(1)).apply(processId.toString, initialIngredientValue)
        _ = verify(testInteractionThreeMock, times(1)).apply(interactionOneIngredientValue, interactionOneIngredientValue)
      } yield succeed
    }

    "reject sensory events after a specified receive period" in {

      val receivePeriod: FiniteDuration = 100 milliseconds

      val recipe: Recipe =
        Recipe("eventReceiveExpirationRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- Future {
          Thread.sleep(receivePeriod.toMillis + 100)
        }
        completed <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("")))
        _ = completed.status shouldBe SensoryEventStatus.ReceivePeriodExpired
      } yield succeed
    }

    "accept sensory events before a specified receive period" in {

      val receivePeriod: FiniteDuration = 10 seconds

      val recipe: Recipe =
        Recipe("eventReceiveInTimeRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        completed <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("")))
      } yield completed.status shouldBe SensoryEventStatus.Completed
    }

    "be able to visualize events that have been fired" in {
      //This test only checks if the graphviz is different, not that the outcome is correct
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        noEventsGraph = baker.getVisualState(processId)
        //System.out.println(noEventsGraph)
        //Handle first event
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
        firstEventGraph <- baker.getVisualState(processId)
        //System.out.println(firstEventGraph)
        _ = noEventsGraph should not be firstEventGraph
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(SecondEvent()))
        secondEventGraph <- baker.getVisualState(processId)
        //System.out.println(secondEventGraph)
        _ = firstEventGraph should not be secondEventGraph
      } yield succeed
    }

    "properly handle a retention period" in {

      val retentionPeriod = 2 seconds

      val recipe: Recipe =
        Recipe("RetentionPeriodRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withRetentionPeriod(retentionPeriod)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        //Should not fail
        _ <- baker.getProcessState(processId)
        _ <- Future {
          Thread.sleep(FiniteDuration(retentionPeriod.toMillis + 1000, TimeUnit.MILLISECONDS).dilated.toMillis)
        }
        //Should fail
        _ <- recoverToSucceededIf[ProcessDeletedException] {
          baker.getProcessState(processId)
        }
      } yield succeed
    }

    "block interaction and log error message if a null ingredient is provided directly by a Interaction" in {
      val recipe =
        Recipe("NullIngredientRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(null)
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(processId, "initialIngredient")
        state <- baker.getProcessState(processId)
        _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
      } yield succeed
    }

    "block interaction and log error message if a null ingredient is provided by an Event provided by a Interaction" in {
      val recipe =
        Recipe("NullIngredientFromEventRecipe")
          .withInteraction(interactionTwo
            .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"))
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionTwoMock.apply(anyString())).thenReturn(EventFromInteractionTwo(null))
        processId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, processId)
        _ <- baker.fireSensoryEventCompleted(processId, RuntimeEvent.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionTwoMock).apply("initialIngredient")
        state <- baker.getProcessState(processId)
        _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
      } yield succeed
    }
  }
}
