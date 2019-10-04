package com.ing.baker.runtime.akka

import java.util.concurrent.TimeUnit
import java.util.{Optional, UUID}

import akka.actor.ActorSystem
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.stream.{ActorMaterializer, Materializer}
import akka.testkit.{TestDuration, TestKit, TestProbe}
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.baker.runtime.common.BakerException._
import com.ing.baker.runtime.common._
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.ing.baker.types.{CharArray, Int32, PrimitiveValue}
import com.typesafe.config.{Config, ConfigFactory}
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

    "throw an ProcessAlreadyExistsException if a baking a process with the same identifier twice" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("DuplicateIdentifierRecipe")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- recoverToSucceededIf[ProcessAlreadyExistsException] {
          baker.bake(recipeId, id)
        }
      } yield succeed
    }

    "throw a NoSuchProcessException when requesting the process state of a non existing process" in {
      for {
        (baker, _) <- setupBakerWithRecipe("NonExistingProcessTest")
        _ <- recoverToSucceededIf[NoSuchProcessException] {
          baker.getRecipeInstanceState(UUID.randomUUID().toString)
        }
      } yield succeed
    }

    "throw a NoSuchProcessException when attempting to fire an event for a non existing process" in {
      for {
        (baker, _) <- setupBakerWithRecipe("NonExistingProcessEventTest")
        event = EventInstance.unsafeFrom(InitialEvent("initialIngredient"))
        response = baker.fireEvent(UUID.randomUUID().toString, event)
        _ <- recoverToSucceededIf[NoSuchProcessException] {
          response.resolveWhenReceived
        }
        _ <- recoverToSucceededIf[NoSuchProcessException] {
          response.resolveWhenCompleted
        }
      } yield succeed
    }

    "throw a IllegalEventException if fired event is not a valid sensory event" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("NonExistingProcessEventTest")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        intercepted <- recoverToExceptionIf[IllegalEventException] {
          baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SomeNotDefinedEvent("bla")))
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield
        state.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue,
            "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "execute an interaction when its ingredient is provided in cluster" in {
      val recipe =
        Recipe("IngredientProvidedRecipeCluster")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)


      val config: Config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          |akka {
          |  actor {
          |    provider = "cluster"
          |  }
          |  remote {
          |    log-remote-lifecycle-events = off
          |    netty.tcp {
          |      hostname = "127.0.0.1"
          |      port = 2552
          |    }
          |  }
          |
          |  cluster {
          |    seed-nodes = ["akka.tcp://remoteTest@127.0.0.1:2552"]
          |    auto-down-unreachable-after = 10s
          |  }
          |}
          |baker.interaction-manager = remote
        """.stripMargin).withFallback(ConfigFactory.load())

      val baker = Baker.akka(config, ActorSystem.apply("remoteTest", config), ActorMaterializer())

      for {
        _ <- baker.addInteractionInstances(mockImplementations)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield
        state.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue,
            "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "Correctly notify on event" in {

      val sensoryEvent = Event(
        name = "sensory-event",
        providedIngredients = Seq(Ingredient[Int]("ingredient-0")),
        maxFiringLimit = None
      )
      val interaction1 = Interaction(
        name = "Interaction1",
        inputIngredients = Seq(Ingredient[Int]("ingredient-0")),
        output = Seq(Event(
          name = "interaction-1-happened",
          providedIngredients = Seq(Ingredient[String]("ingredient-1")),
          maxFiringLimit = None
        ))
      )
      val interaction2 = Interaction(
        name = "Interaction2",
        inputIngredients = Seq(Ingredient[String]("ingredient-1")),
        output = Seq(Event(
          name = "interaction-2-happened",
          providedIngredients = Seq(Ingredient[String]("ingredient-2")),
          maxFiringLimit = None
        ))
      )
      val interaction3 = Interaction(
        name = "Interaction3",
        inputIngredients = Seq(Ingredient[String]("ingredient-2")),
        output = Seq(Event(
          name = "interaction-3-happened",
          providedIngredients = Seq(Ingredient[String]("final")),
          maxFiringLimit = None
        ))
      )

      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteractions(interaction1, interaction2, interaction3)
          .withSensoryEvent(sensoryEvent)

      val interactionInstances = Seq(
        InteractionInstance(
          name = "Interaction1",
          input = Seq(Int32),
          output = None,
          run = _ => Future.successful(Some(EventInstance("interaction-1-happened", Map("ingredient-1" -> PrimitiveValue("data1")))))
        ),
        InteractionInstance(
          name = "Interaction2",
          input = Seq(CharArray),
          output = None,
          run = _ => Future.successful(Some(EventInstance("interaction-2-happened", Map("ingredient-2" -> PrimitiveValue("data2")))))
        ),
        InteractionInstance(
          name = "Interaction3",
          input = Seq(CharArray),
          output = None,
          run = _ => Future.successful(Some(EventInstance("interaction-3-happened", Map("final" -> PrimitiveValue("data3")))))
        )
      )

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, interactionInstances)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveOnEvent(
          recipeInstanceId,
          EventInstance("sensory-event", Map("ingredient-0" -> PrimitiveValue(42))),
          onEvent = "interaction-2-happened")
        _ = completed.eventNames shouldBe
          Seq("sensory-event", "interaction-1-happened", "interaction-2-happened")
        _ = completed.ingredients shouldBe
          Map("ingredient-0" -> PrimitiveValue(42),
            "ingredient-1" -> PrimitiveValue("data1"),
            "ingredient-2" -> PrimitiveValue("data2"))
        _ <- Future(Thread.sleep(100))
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state.ingredients shouldBe
          Map("ingredient-0" -> PrimitiveValue(42),
            "ingredient-1" -> PrimitiveValue("data1"),
            "ingredient-2" -> PrimitiveValue("data2"),
            "final" -> PrimitiveValue("data3"))
      } yield succeed
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionTwoMock).apply(initialIngredientValue)
        _ = verify(testFireTwoEventsInteractionMock).apply(initialIngredientValue)
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, initialIngredientValue)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
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

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        response0 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response0.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")

        response1 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response1.sensoryEventStatus shouldBe SensoryEventStatus.FiringLimitMet
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
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

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        response0 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "abc")
        _ = response0.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")

        response1 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "abc")
        _ = response1.sensoryEventStatus shouldBe SensoryEventStatus.AlreadyReceived
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

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        response0 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response0.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")

        response1 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response1.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock, times(2)).apply(recipeInstanceId.toString, "initialIngredient")

        // This check is added to verify event list is still correct after firing the same event twice
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state.eventNames shouldBe List("InitialEvent", "InteractionOneSuccessful", "InitialEvent", "InteractionOneSuccessful")

        response2 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response2.sensoryEventStatus shouldBe SensoryEventStatus.FiringLimitMet
        _ = verify(testInteractionOneMock, times(2)).apply(recipeInstanceId.toString, "initialIngredient")
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
        val recipeInstanceId = "backwards-compatible-process"
        val order = "123"
        val trackingId = "trackingId"
        val goods = "some goods"

        // mocks
        val shipGoodsMock: ShipGoods = mock[Webshop.ShipGoods]
        val sendInvoiceMock: SendInvoice = mock[Webshop.SendInvoice]
        val manufactureGoodsMock: ManufactureGoods = mock[Webshop.ManufactureGoods]
        val validateOrderMock: ValidateOrder = mock[Webshop.ValidateOrder]

        val implementations = Seq(shipGoodsMock, sendInvoiceMock, manufactureGoodsMock, validateOrderMock).map(InteractionInstance.unsafeFrom(_))

        def createProcess(baker: Baker, recipeId: String): Future[Unit] = {
          for {
            _ <- baker.bake(recipeId, recipeInstanceId)
            // prepare mocks
            _ = when(shipGoodsMock.apply(anyString(), any[CustomerInfo]())).thenReturn(new ShipGoods.GoodsShipped(trackingId))
            _ = when(sendInvoiceMock.apply(any[CustomerInfo]())).thenReturn(new SendInvoice.InvoiceWasSent())
            _ = when(manufactureGoodsMock.apply(anyString())).thenReturn(new ManufactureGoods.GoodsManufactured(goods))
            _ = when(validateOrderMock.apply(anyString(), anyString())).thenReturn(new ValidateOrder.Valid())

            // process the events
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(new CustomerInfoReceived(customerInfo)))
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(new OrderPlaced(order)))
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(new PaymentMade()))
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

          state <- baker.getRecipeInstanceState(recipeInstanceId)
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
        _ <- baker.addInteractionInstances(mockImplementations)

        compiledRecipe = RecipeCompiler.compileRecipe(recipe)
        recipeId <- baker.addRecipe(compiledRecipe)

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testOptionalIngredientInteractionMock).apply(ingredientValue, Optional.empty(), Option.empty, Option.empty, initialIngredientValue)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
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

        recipeInstanceId = UUID.randomUUID().toString

        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(UnboxedProviderEvent(initialIngredientValue, initialIngredientValue, initialIngredientValue)))

        _ = verify(testOptionalIngredientInteractionMock).apply(java.util.Optional.of(initialIngredientValue), Optional.empty(), Some(initialIngredientValue), Option.empty, initialIngredientValue)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "missingJavaOptional" -> initialIngredientValue, "missingScalaOptional" -> initialIngredientValue)
    }

    "notify a registered event listener of events" in {
      val listenerMock = mock[(String, EventInstance) => Unit]
      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
      val recipe =
        Recipe("EventListenerRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ <- baker.registerEventListener("EventListenerRecipe", listenerMock)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(listenerMock).apply(mockitoEq(recipeInstanceId.toString), argThat(new RuntimeEventMatcher(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))))
        _ = verify(listenerMock).apply(mockitoEq(recipeInstanceId.toString), argThat(new RuntimeEventMatcher(EventInstance.unsafeFrom(InteractionOneSuccessful(interactionOneIngredientValue)))))
      } yield succeed
    }

    "return a list of events that where caused by a sensory event" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("SensoryEventDeltaRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        response = baker.fireEvent(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        confirmReceived <- response.resolveWhenReceived
        _ = confirmReceived shouldBe SensoryEventStatus.Received
        confirmCompleted <- response.resolveWhenCompleted
        _ = confirmCompleted.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = confirmCompleted.ingredients.keys should contain only(
          "initialIngredient",
          "sievedIngredient",
          "interactionOneIngredient",
          "interactionTwoIngredient",
          "interactionThreeIngredient"
        )
      } yield confirmCompleted.eventNames should contain only(
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "execute an interaction when both ingredients are provided (join situation)" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("JoinRecipeForIngredients")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, initialIngredientValue)
        _ = verify(testInteractionTwoMock).apply(initialIngredientValue)
        _ = verify(testInteractionThreeMock).apply(interactionOneIngredientValue, interactionTwoIngredientValue)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe afterInitialState
    }

    "execute an interaction when two events occur (join situation)" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("JoinRecipeForEvents")

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        response0 = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        response1 = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        _ <- response0
        _ <- response1

        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock).apply("initialIngredient")
        _ = verify(testInteractionThreeMock).apply("interactionOneIngredient",
          "interactionTwoIngredient")
        _ = verify(testInteractionFourMock).apply()
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe finalState
    }

    "execute an interaction when one of the two events occur (OR situation)" in {
      val recipe = Recipe("ORPreconditionedRecipeForEvents")
        .withInteractions(interactionFour
          .withRequiredOneOfEvents(initialEvent, secondEvent))
        .withSensoryEvents(initialEvent, secondEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        firstrecipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, firstrecipeInstanceId)
        // Fire one of the events for the first process
        _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionFourMock).apply()
        // reset interaction mocks and fire the other event for the second process
        _ = resetMocks()
        secondrecipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, secondrecipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(secondrecipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
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
        firstrecipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, firstrecipeInstanceId)
        // Fire one of the events for the first process
        _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionFourMock, times(0)).apply()
        _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(ThirdEvent()))
        _ = verify(testInteractionFourMock).apply()
      } yield succeed
    }

    "execute two interactions which depend on same ingredient (fork situation)" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock).apply("initialIngredient")
      } yield succeed
    }

    "execute again after first execution completes and ingredient is produced again" in {

      for {
        (baker, recipeId) <- setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionOneMock, times(1)).apply(recipeInstanceId.toString, "initialIngredient")
        _ = verify(testInteractionTwoMock, times(1)).apply("initialIngredient")
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        _ = verify(testInteractionOneMock, times(2)).apply(recipeInstanceId.toString, "initialIngredient")
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        start = System.currentTimeMillis()
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
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
        recipeInstanceId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(recipeInstanceId.toString, firstData)).thenReturn(Future.successful(InteractionOneSuccessful(firstResponse)))
        _ = when(testInteractionOneMock.apply(recipeInstanceId.toString, secondData)).thenReturn(Future.successful(InteractionOneSuccessful(secondResponse)))
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Fire the first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(firstData)))
        state0 <- baker.getRecipeInstanceState(recipeInstanceId)
        //Check that the first response returned
        _ = state0.ingredients shouldBe ingredientMap(
          "initialIngredient" -> firstData,
          "interactionOneIngredient" -> firstResponse,
          "sievedIngredient" -> sievedIngredientValue,
          "interactionTwoIngredient" -> interactionTwoIngredientValue,
          "interactionThreeIngredient" -> interactionThreeIngredientValue
        )
        //Fire the second event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(secondData)))
        //Check that the second response is given
        state <- baker.getRecipeInstanceState(recipeInstanceId)
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, initialIngredientValue)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state.ingredients shouldBe ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneIngredient" -> interactionOneIngredientValue)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verifyZeroInteractions(testInteractionOneMock)
      } yield succeed
    }

    "not throw an exception when an event is fired and a resulting interactions fails" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FailingInteraction")
        _ = when(testInteractionOneMock.apply(anyString, anyString()))
          .thenThrow(new RuntimeException(errorMessage))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield succeed
    }

    "not crash when one process crashes but the other does not" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CrashTestRecipe")

        firstrecipeInstanceId = UUID.randomUUID().toString
        secondrecipeInstanceId = UUID.randomUUID().toString
        _ = when(testInteractionOneMock.apply(firstrecipeInstanceId.toString, initialIngredientValue))
          .thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
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

    "keep the input data in accumulated state even if the interactions dependent on this event fail to execute" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("StatePersistentTestRecipe")
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

    "retry an interaction with incremental backoff if configured to do so" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FailingInteractionWithBackof")
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException(errorMessage))

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        //Thread.sleep is needed since we need to wait for the expionental back of
        //100ms should be enough since it waits 20ms and then 40 ms
        _ <- Future {
          Thread.sleep(200)
        }
        //Since it can be called up to 3 times it should have been called 3 times in the 100ms
        _ = verify(testInteractionOneMock, times(4)).apply(recipeInstanceId.toString, initialIngredientValue)
      } yield succeed
    }

    "not execute the failing interaction again each time after some other unrelated event is fired" in {
      /* This test FAILS because passportData FAIL_DATA is included in the marking while it should not! (?)
       * The fact that it is in the marking forces failingUploadPassport to fire again when second event fires!
       */
      for {
        (baker, recipeId) <- setupBakerWithRecipe("ShouldNotReExecute")
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- Future {
          Thread.sleep(50)
        }
        state <- baker.getRecipeInstanceState(recipeInstanceId)
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- Future {
          Thread.sleep(50)
        }
        //Since the defaultEventExhaustedName is set the retryExhaustedEventName of interactionOne will be picked.
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.eventNames should not contain interactionOne.retryExhaustedEventName
    }

    "fire a specified failure event for an interaction immediately after it fails" in {

      val recipe = Recipe("ImmediateFailureEvent")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(FireEventAfterFailure()))

      when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new RuntimeException("Some failure happened"))

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)

        listenerMock = mock[(String, EventInstance) => Unit]
        _ <- baker.registerEventListener("ImmediateFailureEvent", listenerMock)

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- Future {
          Thread.sleep(50)
        }
        _ = verify(listenerMock).apply(mockitoEq(recipeInstanceId.toString), argThat(new RuntimeEventMatcher(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))))
        _ = verify(listenerMock).apply(mockitoEq(recipeInstanceId.toString), argThat(new RuntimeEventMatcher(EventInstance(interactionOne.retryExhaustedEventName, Map.empty))))

        state <- baker.getRecipeInstanceState(recipeInstanceId)
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

    "be able to return all occurred events" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
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
        recipeInstanceIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
        _ <- Future.traverse(recipeInstanceIds)(baker.bake(recipeId, _))
        index <- baker.getAllRecipeInstancesMetadata
      } yield index.map(_.recipeInstanceId) shouldBe recipeInstanceIds
    }

    "be able to return an index of all processes in local/inmemory mode" in {

      val nrOfProcesses = 200

      for {
        (baker, recipeId) <- setupBakerWithRecipe("IndexTestLocal")
        recipeInstanceIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
        _ <- Future.traverse(recipeInstanceIds)(baker.bake(recipeId, _))
        index <- baker.getAllRecipeInstancesMetadata
      } yield index.map(_.recipeInstanceId) shouldBe recipeInstanceIds
    }

    //Only works if persistence actors are used (think cassandra)
    "recover the state of a process from a persistence store" in {
      val system1 = ActorSystem("persistenceTest1", localLevelDBConfig("persistenceTest1"))
      val mat1 = ActorMaterializer.create(system1)
      val recoveryRecipeName = "RecoveryRecipe"
      val recipeInstanceId = UUID.randomUUID().toString

      val compiledRecipe = RecipeCompiler.compileRecipe(getRecipe(recoveryRecipeName))

      val first = (for {
        baker1 <- setupBakerWithNoRecipe()(system1, mat1)
        recipeId <- baker1.addRecipe(compiledRecipe)
        _ <- baker1.bake(recipeId, recipeInstanceId)
        _ <- baker1.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- baker1.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        state <- baker1.getRecipeInstanceState(recipeInstanceId)
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
          _ <- baker2.addInteractionInstances(mockImplementations)
          state <- baker2.getRecipeInstanceState(recipeInstanceId)
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
    }

    "acknowledge the first and final event while rest processing failed" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("AcknowledgeThefirst")
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

    "bind multi transitions correctly even if ingredient name overlaps" in {
      //This test is part of the ExecutionSpec and not the Compiler spec because the only correct way to validate
      //for this test is to check if Baker calls the mocks.
      //If there is a easy way to validate the created petrinet by the compiler it should be moved to the compiler spec.
      for {
        (baker, recipeId) <- setupBakerWithRecipe("OverlappingMultiIngredients")

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
        recipeInstanceId = UUID.randomUUID().toString

        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testInteractionOneMock, times(1)).apply(recipeInstanceId.toString, initialIngredientValue)
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- Future {
          Thread.sleep(receivePeriod.toMillis + 100)
        }
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
        _ = completed.sensoryEventStatus shouldBe SensoryEventStatus.ReceivePeriodExpired
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
      } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
    }

    "be able to visualize events that have been fired" in {
      //This test only checks if the graphviz is different, not that the outcome is correct
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        noEventsGraph = baker.getVisualState(recipeInstanceId)
        //System.out.println(noEventsGraph)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        firstEventGraph <- baker.getVisualState(recipeInstanceId)
        //System.out.println(firstEventGraph)
        _ = noEventsGraph should not be firstEventGraph
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        secondEventGraph <- baker.getVisualState(recipeInstanceId)
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Should not fail
        _ <- baker.getRecipeInstanceState(recipeInstanceId)
        _ <- Future {
          Thread.sleep(FiniteDuration(retentionPeriod.toMillis + 1000, TimeUnit.MILLISECONDS).dilated.toMillis)
        }
        //Should fail
        _ <- recoverToSucceededIf[ProcessDeletedException] {
          baker.getRecipeInstanceState(recipeInstanceId)
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
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
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
