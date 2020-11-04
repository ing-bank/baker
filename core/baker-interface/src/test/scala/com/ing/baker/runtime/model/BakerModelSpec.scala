package com.ing.baker.runtime.model

import java.util.UUID

import cats.effect.{ConcurrentEffect, IO, Resource, Sync}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, ProcessAlreadyExistsException}
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceF}
import com.ing.bakery.utils.BakeryFunSpec
import org.mockito.Matchers.anyString
import org.mockito.Mockito.{verify, when}
import org.scalatest.{BeforeAndAfter, ConfigMap}
import org.scalatest.matchers.should.Matchers
import com.ing.baker.runtime.model.ScalaDSLRuntime._

import scala.reflect.ClassTag

abstract class BakerModelSpec[F[_]]
  extends BakeryFunSpec[F]
    with BakerModelFixtures[F]
  with Matchers
    with BeforeAndAfter {

  before {
    resetMocks()
  }

  def runEnquireTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {
    test("return recipe if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnRecipe", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipe <- baker.getRecipe(recipeId)
      } yield recipe.compiledRecipe.name shouldBe "returnRecipe"
    }

    test("return all recipes if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnAllRecipes", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2")))
        recipes <- baker.getAllRecipes
        _ = recipes.size shouldBe 2
        _ = recipes(recipeId).compiledRecipe.name shouldBe "returnAllRecipes"
        _ = recipes(recipeId2).compiledRecipe.name shouldBe "returnAllRecipes2"
      } yield succeed
    }

    test("return no errors of a recipe with no errors if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnHealthRecipe", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipeInformation <- baker.getRecipe(recipeId)
        _ = assert(recipeInformation.compiledRecipe.recipeId == recipeId && recipeInformation.errors.isEmpty)
      } yield succeed
    }

    test("return no errors of all recipes if none contain errors if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnHealthAllRecipe", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
        recipeInformations <- baker.getAllRecipes
        _ = recipeInformations.size shouldBe 2
        _ = recipeInformations.get(recipeId)
          .foreach(r => assert(r.compiledRecipe.recipeId == recipeId && r.errors.isEmpty))
        _ = recipeInformations.get(recipeId2)
          .foreach(r => assert(r.compiledRecipe.recipeId == recipeId2 && r.errors.isEmpty))
      } yield succeed
    }
  }

  def runSetupTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {

    test("correctly load extensions when specified in the configuration") { context =>
      val simpleRecipe = RecipeCompiler.compileRecipe(Recipe("SimpleRecipe")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent))

      for {
        baker <- context.setupBakerWithNoRecipe
        _ <- baker.addInteractionInstances(mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful("foobar")))
        recipeId <- baker.addRecipe(simpleRecipe)
        recipeInstanceId = java.util.UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, initialEvent.instance("initialIngredient"))
      } yield succeed
    }

    test("providing implementations in a sequence") { context =>
      context.setupBakerWithNoRecipe.flatMap {
        _.addInteractionInstances(mockImplementations).map(_ => succeed)
      }
    }

    test("providing an implementation with the class simplename same as the interaction") { context =>
      context.setupBakerWithNoRecipe.flatMap {
        _.addInteractionInstances(mockImplementations).map(_ => succeed)
      }
    }

    test("providing an implementation for a renamed interaction") { context =>
      val recipe = Recipe("simpleNameImplementationWithRename")
        .withInteraction(interactionOne.withName("interactionOneRenamed"))
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.setupBakerWithNoRecipe
        _ <- baker.addInteractionInstance(InteractionInstanceF.unsafeFrom(new InteractionOneSimple()))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("providing an implementation with a name field") { context =>
      val recipe = Recipe("fieldNameImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.setupBakerWithNoRecipe
        _ <- baker.addInteractionInstance(InteractionInstanceF.unsafeFrom(new InteractionOneFieldName()))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("providing the implementation in a sequence with the interface its implementing with the correct name") { context =>

      val recipe = Recipe("interfaceImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.buildBaker
        _ <- baker.addInteractionInstance(InteractionInstanceF.unsafeFrom(new InteractionOneInterfaceImplementation()))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("the recipe contains complex ingredients that are serializable") { context =>
      val recipe = Recipe("complexIngredientInteractionRecipe")
        .withInteraction(interactionWithAComplexIngredient)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.buildBaker
        _ <- baker.addInteractionInstance(InteractionInstanceF.unsafeFrom(mock[ComplexIngredientInteraction]))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("throw a exception when an invalid recipe is given") { context =>

      val recipe = Recipe("NonProvidedIngredient")
        .withInteraction(interactionOne)
        .withSensoryEvent(secondEvent)

      for {
        baker <- context.buildBaker
        _ <- baker.addInteractionInstances(mockImplementations)
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe)).attempt.map {
          case Left(e) => e should have('message("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction"))
          case Right(_) => fail("Adding a recipe should fail")
        }
      } yield succeed
    }

    test("throw a exception when a recipe does not provide an implementation for an interaction") { context =>

      val recipe = Recipe("MissingImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      for {
        baker <- context.buildBaker
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe)).attempt.map {
          case Left(e) => e should have('message("No implementation provided for interaction: InteractionOne"))
          case Right(_) => fail("Adding a recipe should fail")
        }
      } yield succeed
    }

    test("throw a exception when a recipe provides an implementation for an interaction and does not comply to the Interaction") { context =>

      val recipe = Recipe("WrongImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      for {
        baker <- context.buildBaker
        _ <- baker.addInteractionInstance(InteractionInstanceF.unsafeFrom(new InteractionOneWrongApply()))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe)).attempt.map {
          case Left(e) => e should have('message("No implementation provided for interaction: InteractionOne"))
          case Right(_) => fail("Adding an interaction should fail")
        }
      } yield succeed
    }
  }

  def runExecutionSemanticsTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {

    test("bake a process successfully if baking for the first time") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("FirstTimeBaking")
        (baker, recipeId) = bakerAndRecipeId
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
      } yield succeed
    }

    test("throw an ProcessAlreadyExistsException if baking a process with the same identifier twice") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("DuplicateIdentifierRecipe")
        (baker, recipeId) = bakerAndRecipeId
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.bake(recipeId, id).attempt.map {
          case Left(_: ProcessAlreadyExistsException) => succeed
          case _ => fail("Baking again should fail")
        }
      } yield succeed
    }

    test("throw a NoSuchProcessException when requesting the process state for a process that does not exist") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("NonExistingProcessTest")
        (baker, _) = bakerAndRecipeId
        _ <- baker.getRecipeInstanceState(UUID.randomUUID().toString).attempt.map {
          case Left(_: NoSuchProcessException) => succeed
          case _ => fail("Should have thrown a NoSuchProcessException error")
        }
      } yield succeed
    }

    test("throw a NoSuchProcessException when attempting to fire an event for a process that does not exist") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("NonExistingProcessEventTest")
        (baker, _) = bakerAndRecipeId
        event = EventInstance.unsafeFrom(InitialEvent("initialIngredient"))
        response = baker.fireEvent(UUID.randomUUID().toString, event)
        _ <- response.resolveWhenReceived.attempt.map { x =>
          println(Console.MAGENTA + x + Console.RESET)
          x match {
            case Left(_: NoSuchProcessException) => succeed
            case _ => fail("Should have thrown a NoSuchProcessException error")
          }
        }
        _ <- response.resolveWhenCompleted.attempt.map { x =>
          println(Console.MAGENTA + x + Console.RESET)
          x match {
            case Left(_: NoSuchProcessException) => succeed
            case _ => fail("Should have thrown a NoSuchProcessException error")
          }
        }
      } yield succeed
    }

    test("throw a IllegalEventException if the event fired is not a valid sensory event") { context =>
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("NonExistingProcessEventTest")
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SomeNotDefinedEvent("bla"))).attempt.map {
          case Left(e: IllegalEventException) =>
            e.getMessage should startWith("No event with name 'SomeNotDefinedEvent' found in recipe 'NonExistingProcessEventTest")
          case _ => fail("Should have thrown an IllegalEventException error")
        }
      } yield succeed
    }

    test("execute an interaction when its ingredient is provided") { context =>
      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        bakerWithRecipe <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerWithRecipe
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield
        state.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue,
            "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    /*
    {

      test("execute an interaction when its ingredient is provided in cluster") { context =>
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
            |      port = 2555
            |    }
            |  }
            |
            |  cluster {
            |    seed-nodes = ["akka.tcp://remoteTest@127.0.0.1:2555"]
            |    auto-down-unreachable-after = 10s
            |  }
            |}
        """.stripMargin).withFallback(ConfigFactory.load())

        val baker = AkkaBaker(config, ActorSystem.apply("remoteTest", config))

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

      test("Correctly notify on event") { context =>

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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, interactionInstances)
          (baker, recipeId) = bakerAndRecipeId
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

      test("fire an event twice if two interactions fire it") { context =>
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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
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

      "only allow a sensory event be fired once" when {
        test("the max firing limit is set to one") { context =>
          val recipe =
            Recipe("maxFiringLimitOfOneOnSensoryEventRecipe")
              .withInteraction(interactionOne)
              .withSensoryEvent(initialEvent.withMaxFiringLimit(1))

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId

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
      }

      test("not allow a sensory event be fired twice with the same correlation id") { context =>
        val recipe =
          Recipe("correlationIdSensoryEventRecipe")
            .withInteraction(interactionOne)
            .withSensoryEvent(initialEvent)

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId

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


      "only allow a sensory event be fired twice" when {
        test("the max firing limit is set to two") { context =>
          val recipe =
            Recipe("maxFiringLimitOfTwoOnSensoryEventRecipe")
              .withInteraction(interactionOne)
              .withSensoryEvent(initialEvent.withMaxFiringLimit(2))

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId

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
      }

      "backwards compatibility in serialization of case class ingredients, THIS TEST IS BROKEN FIX ME!" ignore {

        val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))

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
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, implementations)(actorSystem)
          (baker, recipeId) = bakerAndRecipeId
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

      test("execute an interaction with Optional set to empty when its ingredient is provided") { context =>
        val ingredientValue: Optional[String] = java.util.Optional.of("optionalWithValue")

        val recipe =
          Recipe("IngredientProvidedRecipeWithEmptyOptionals")
            .withInteraction(
              interactionWithOptionalIngredients
                .withPredefinedIngredients(("missingJavaOptional", ingredientValue)))
            .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem)

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

      test("execute an interaction with Optional boxed when its ingredient is provided as unboxed") { context =>
        val recipe =
          Recipe("IngredientProvidedRecipeWithUnboxedOptionals")
            .withInteraction(
              interactionWithOptionalIngredients)
            .withSensoryEvent(unboxedProviderEvent)

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId

          recipeInstanceId = UUID.randomUUID().toString

          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(UnboxedProviderEvent(initialIngredientValue, initialIngredientValue, initialIngredientValue)))

          _ = verify(testOptionalIngredientInteractionMock).apply(java.util.Optional.of(initialIngredientValue), Optional.empty(), Some(initialIngredientValue), Option.empty, initialIngredientValue)
          state <- baker.getRecipeInstanceState(recipeInstanceId)
        } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "missingJavaOptional" -> initialIngredientValue, "missingScalaOption" -> initialIngredientValue)
      }

      test("notify a registered event listener of events") { context =>
        val listenerMock = mock[(RecipeEventMetadata, EventInstance) => Unit]
        when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
        val recipe =
          Recipe("EventListenerRecipe")
            .withInteraction(interactionOne)
            .withSensoryEvent(initialEvent)

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
          _ <- baker.registerEventListener("EventListenerRecipe", listenerMock)
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
          _ = verify(listenerMock).apply(mockitoEq(RecipeEventMetadata(recipeId, recipe.name, recipeInstanceId.toString)), argThat(new RuntimeEventMatcher(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))))
          _ = verify(listenerMock).apply(mockitoEq(RecipeEventMetadata(recipeId, recipe.name, recipeInstanceId.toString)), argThat(new RuntimeEventMatcher(EventInstance.unsafeFrom(InteractionOneSuccessful(interactionOneIngredientValue)))))
        } yield succeed
      }

      test("return a list of events that where caused by a sensory event") { context =>
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("SensoryEventDeltaRecipe")
          (baker, recipeId) = bakerAndRecipeId
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

      "execute an interaction" when {
        test("its ingredient is provided and the interaction is renamed") { context =>
          val recipe =
            Recipe("IngredientProvidedRecipeWithRename")
              .withInteraction(interactionOne.withName("interactionOneRenamed"))
              .withSensoryEvent(initialEvent)

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
            _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
            recipeInstanceId = UUID.randomUUID().toString
            _ <- baker.bake(recipeId, recipeInstanceId)
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
            _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
            state <- baker.getRecipeInstanceState(recipeInstanceId)
          } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
        }

        test("both ingredients are provided (JOIN situation)") { context =>
          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe("JoinRecipeForIngredients")
          (baker, recipeId) = bakerAndRecipeId
            recipeInstanceId = UUID.randomUUID().toString
            _ <- baker.bake(recipeId, recipeInstanceId)
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
            _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, initialIngredientValue)
            _ = verify(testInteractionTwoMock).apply(initialIngredientValue)
            _ = verify(testInteractionThreeMock).apply(interactionOneIngredientValue, interactionTwoIngredientValue)
            state <- baker.getRecipeInstanceState(recipeInstanceId)
          } yield state.ingredients shouldBe afterInitialState
        }

        test("two events occur (JOIN situation)") { context =>
          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe("JoinRecipeForEvents")
          (baker, recipeId) = bakerAndRecipeId

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

        test("one of the two events occur (OR situation)") { context =>
          val recipe = Recipe("ORPreconditionedRecipeForEvents")
            .withInteractions(interactionFour
              .withRequiredOneOfEvents(initialEvent, secondEvent))
            .withSensoryEvents(initialEvent, secondEvent)

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
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

        test("one of the two events occur with two OR conditions (OR situation 2)") { context =>
          val recipe = Recipe("ORPreconditionedRecipeForEvents2")
            .withInteractions(interactionFour
              .withRequiredOneOfEvents(initialEvent, secondEvent)
              .withRequiredOneOfEvents(thirdEvent, fourthEvent))
            .withSensoryEvents(initialEvent, secondEvent, thirdEvent, fourthEvent)

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
            firstrecipeInstanceId = UUID.randomUUID().toString
            _ <- baker.bake(recipeId, firstrecipeInstanceId)
            // Fire one of the events for the first process
            _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
            _ = verify(testInteractionFourMock, times(0)).apply()
            _ <- baker.fireEventAndResolveWhenCompleted(firstrecipeInstanceId, EventInstance.unsafeFrom(ThirdEvent()))
            _ = verify(testInteractionFourMock).apply()
          } yield succeed
        }
      }

      test("execute two interactions which depend on same the ingredient (FORK situation)") { context =>
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")
          (baker, recipeId) = bakerAndRecipeId
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
          _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
          _ = verify(testInteractionTwoMock).apply("initialIngredient")
        } yield succeed
      }

      test("execute again after first execution completes and the ingredient is produced again") { context =>

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("MultipleInteractionsFromOneIngredient")
          (baker, recipeId) = bakerAndRecipeId
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

      test("fire parallel transitions simultaneously") { context =>
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("ParallelExecutionRecipe")
          (baker, recipeId) = bakerAndRecipeId
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

      test("update the state with new data if an event occurs twice") { context =>

        val firstData: String = "firstData"
        val secondData: String = "secondData"
        val firstResponse = "firstResponse"
        val secondResponse = "secondResponse"

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("UpdateTestRecipe")
          (baker, recipeId) = bakerAndRecipeId
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

      test("only fire an interaction once if it has a maximum interaction count of one") { context =>

        val recipe = Recipe("FiringLimitTestRecipe")
          .withInteractions(
            interactionOne
              .withEventOutputTransformer(interactionOneSuccessful, Map("interactionOneOriginalIngredient" -> "interactionOneIngredient"))
              .withMaximumInteractionCount(1))
          .withSensoryEvent(initialEvent)

        when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
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

      test("not throw an exception when an event is fired and a resulting interactions fails") { context =>
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("FailingInteraction")
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
          bakerAndRecipeId<- context.setupBakerWithRecipe("CrashTestRecipe")
          (baker, recipeId) = bakerAndRecipeId

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

      test("keep the input data in accumulated state even if the interactions dependent on this event fail to execute") { context =>
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("StatePersistentTestRecipe")
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
          bakerAndRecipeId<- context.setupBakerWithRecipe("FailingInteractionWithBackoff")
          (baker, recipeId) = bakerAndRecipeId
          _ = when(testInteractionOneMock.apply(anyString(), anyString()))
            .thenThrow(new RuntimeException(errorMessage))

          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

          //Thread.sleep is needed since we need to wait for the exponential back-off
          //100ms should be enough since it waits 20ms and then 40 ms
          _ <- Future {
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
          bakerAndRecipeId<- context.setupBakerWithRecipe("ShouldNotReExecute")
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
          .withInteractions(interactionOne.withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
            initialDelay = 10 milliseconds,
            maximumRetries = 1,
            fireRetryExhaustedEvent = Some(None))))

        when(testInteractionOneMock.apply(anyString(), anyString())).thenThrow(new IllegalStateException())

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
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
          .withInteractions(interactionOne.withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
            initialDelay = 10 milliseconds,
            maximumRetries = 1,
            fireRetryExhaustedEvent = Some(None))))

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
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

      "be able to return" when {
        test("all occurred events") { context =>
          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe("CheckEventRecipe")
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

        test("an index of all processes in cluster mode") { context =>
          val journalId = java.util.UUID.randomUUID().toString
          val indexTestSystem = ActorSystem("indexTest", clusterLevelDBConfig(
            actorSystemName = "indexTest",
            port = 3005,
            journalPath = s"target/journal-$journalId",
            snapshotsPath = s"target/snapshots-$journalId"))
          val nrOfProcesses = 200

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe("IndexTestCluster")(indexTestSystem)
          (baker, recipeId) = bakerAndRecipeId
            recipeInstanceIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
            _ <- Future.traverse(recipeInstanceIds)(baker.bake(recipeId, _))
            index <- baker.getAllRecipeInstancesMetadata
          } yield index.map(_.recipeInstanceId) shouldBe recipeInstanceIds
        }

        test("an index of all processes in local/in-memory mode") { context =>

          val nrOfProcesses = 200

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe("IndexTestLocal")
          (baker, recipeId) = bakerAndRecipeId
            recipeInstanceIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
            _ <- Future.traverse(recipeInstanceIds)(baker.bake(recipeId, _))
            index <- baker.getAllRecipeInstancesMetadata
          } yield index.map(_.recipeInstanceId) shouldBe recipeInstanceIds
        }
      }

      //Only works if persistence actors are used (think cassandra)
      test("recover the state of a process from a persistence store") { context =>
        val system1 = ActorSystem("persistenceTest1", localLevelDBConfig("persistenceTest1"))
        val recoveryRecipeName = "RecoveryRecipe"
        val recipeInstanceId = UUID.randomUUID().toString

        val compiledRecipe = RecipeCompiler.compileRecipe(getRecipe(recoveryRecipeName))

        val first = (for {
          baker1 <- setupBakerWithNoRecipe()(system1)
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
          val baker2 = AkkaBaker(ConfigFactory.load(), system2)
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

      test("acknowledge the first event, not wait on the rest") { context =>
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("NotWaitForTheRest")
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
          bakerAndRecipeId<- context.setupBakerWithRecipe("AcknowledgeThefirst")
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
          bakerAndRecipeId<- context.setupBakerWithRecipe("OverlappingMultiIngredients")
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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
          recipeInstanceId = UUID.randomUUID().toString

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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- Future {
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
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
        } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
      }

      test("be able to visualize events that have been fired") { context =>
        //This test only checks if the graphviz is different, not that the outcome is correct
        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe("CheckEventRecipe")
          (baker, recipeId) = bakerAndRecipeId
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

      test("properly handle a retention period") { context =>

        val retentionPeriod = 2 seconds

        val recipe: Recipe =
          Recipe("RetentionPeriodRecipe")
            .withSensoryEvents(initialEvent)
            .withInteractions(interactionOne)
            .withRetentionPeriod(retentionPeriod)

        for {
          bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
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

      "block interaction and log error message" when {
        test("a null ingredient is provided directly by an interaction") { context =>
          val recipe =
            Recipe("NullIngredientRecipe")
              .withInteraction(interactionOne)
              .withSensoryEvent(initialEvent)

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
          (baker, recipeId) = bakerAndRecipeId
            _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(null)
            recipeInstanceId = UUID.randomUUID().toString
            _ <- baker.bake(recipeId, recipeInstanceId)
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
            _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
            state <- baker.getRecipeInstanceState(recipeInstanceId)
            _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
          } yield succeed
        }

        test("a null ingredient is provided by an event provided by an interaction") { context =>
          val recipe =
            Recipe("NullIngredientFromEventRecipe")
              .withInteraction(interactionTwo
                .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"))
              .withSensoryEvent(initialEvent)

          for {
            bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
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
    */
  }

  case class Context(buildBaker: F[Baker[F]]) {

    def setupBakerWithRecipe(recipeName: String, appendUUIDToTheRecipeName: Boolean = true)(implicit effect: Sync[F], classTag: ClassTag[F[Any]]): F[(Baker[F], String)] = {
      val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
      val recipe = getRecipe(newRecipeName)
      for {
        _ <- setupMockResponse
        bakerAndRecipeId <- setupBakerWithRecipe(recipe, mockImplementations)
      } yield bakerAndRecipeId
    }

    def setupBakerWithRecipe(recipe: Recipe, implementations: Seq[InteractionInstanceF[F]])(implicit effect: Sync[F]): F[(Baker[F], String)] = {
      for {
        baker <- buildBaker
        _ <- baker.addInteractionInstances(implementations)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield (baker, recipeId)
    }

    def setupBakerWithNoRecipe(implicit effect: Sync[F], classTag: ClassTag[F[Any]]): F[Baker[F]] = {
      for {
        _ <- setupMockResponse
        baker <- buildBaker
        _ <- baker.addInteractionInstances(mockImplementations)
      } yield baker
    }

  }

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = Unit

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext]

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
