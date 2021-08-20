package com.ing.baker.runtime.model

import java.util.UUID

import cats.effect.ConcurrentEffect
import cats.implicits._
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, ProcessAlreadyExistsException, ProcessDeletedException}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceInput, RecipeEventMetadata}
import com.ing.baker.types.{CharArray, Int32, PrimitiveValue}
import org.mockito.Matchers.{eq => mockitoEq, _}
import org.mockito.Mockito._

import scala.concurrent.duration._
import scala.reflect.ClassTag

trait BakerModelSpecExecutionSemanticsTests[F[_]] { self: BakerModelSpec[F] =>

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
        _ <- response.resolveWhenReceived.attempt.map {
          case Left(_: NoSuchProcessException) => succeed
          case _ => fail("Should have thrown a NoSuchProcessException error")
        }
        _ <- response.resolveWhenCompleted.attempt.map {
          case Left(_: NoSuchProcessException) => succeed
          case _ => fail("Should have thrown a NoSuchProcessException error")
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

      val interactionInstances = List(
        InteractionInstance.build[F](
          _name = "Interaction1",
          _input = Seq(InteractionInstanceInput(Option.empty, Int32)),
          _output = None,
          _run = _ => effect.pure(Some(EventInstance("interaction-1-happened", Map("ingredient-1" -> PrimitiveValue("data1")))))
        ),
        InteractionInstance.build[F](
          _name = "Interaction2",
          _input = Seq(InteractionInstanceInput(Option.empty, CharArray)),
          _output = None,
          _run = _ => effect.pure(Some(EventInstance("interaction-2-happened", Map("ingredient-2" -> PrimitiveValue("data2")))))
        ),
        InteractionInstance.build[F](
          _name = "Interaction3",
          _input = Seq(InteractionInstanceInput(Option.empty, CharArray)),
          _output = None,
          _run = _ => effect.pure(Some(EventInstance("interaction-3-happened", Map("final" -> PrimitiveValue("data3")))))
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
        _ = completed.eventNames.toSet shouldBe
          Set("sensory-event", "interaction-1-happened", "interaction-2-happened")
        _ = completed.ingredients shouldBe
          Map("ingredient-0" -> PrimitiveValue(42),
            "ingredient-1" -> PrimitiveValue("data1"),
            "ingredient-2" -> PrimitiveValue("data2"))
        _ <- timer.sleep(100.millis).to[F]
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
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenReturn(effect.pure(InteractionOneSuccessful("data")))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionTwoMock).apply(initialIngredientValue)
        _ = verify(testFireTwoEventsInteractionMock).apply(initialIngredientValue)
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, initialIngredientValue)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.eventNames should contain allOf("InitialEvent", "Event1FromInteractionSeven", "EventFromInteractionTwo", "InteractionOneSuccessful")
    }

    test("only allow a sensory event be fired once when the max firing limit is set to one") { context =>
      val recipe =
        Recipe("maxFiringLimitOfOneOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(1))

      for {
        bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        response0 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response0.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")

        response1 <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = response1.sensoryEventStatus shouldBe SensoryEventStatus.FiringLimitMet
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
      } yield succeed
    }

    test("not allow a sensory event be fired twice with the same correlation id") { context =>
      val recipe =
        Recipe("correlationIdSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))

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

    test("only allow a sensory event be fired twice when the max firing limit is set to two") { context =>
      val recipe =
        Recipe("maxFiringLimitOfTwoOnSensoryEventRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent.withMaxFiringLimit(2))

      for {
        bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId

        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))

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


    test("notify a registered event listener of events") { context =>
      val listenerMock = mock[(RecipeEventMetadata, EventInstance) => Unit]
      when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
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

    test("return a list of events that were caused by a sensory event") { context =>
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

    /* TODO (see BakerF TODO)
    test("properly handle a retention period") { context =>

      val retentionPeriod = 300.millis

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
        _ <- baker.getRecipeInstanceState(recipeInstanceId)
        _ <- timer.sleep((retentionPeriod.toMillis + 100).millis).to[F]
        result <- effect.attempt(baker.getRecipeInstanceState(recipeInstanceId))
      } yield result match {
        case Left(_: ProcessDeletedException) => succeed
        case a => fail(s"Should have failed with ProcessDeletedException, instead got: $a")
      }
    }
     */
  }
}
