package com.ing.baker.runtime.model

import java.util.{Optional, UUID}
import cats.effect.ConcurrentEffect
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.RecipeVisualStyle
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.scaladsl.EventInstance
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock

import scala.reflect.ClassTag
import scala.concurrent.duration._
import cats.implicits._
import com.ing.baker.runtime.common.RecipeRecord

trait BakerModelSpecEdgeCasesTests[F[_]] { self: BakerModelSpec[F] =>

  def runEdgeCasesTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {
    test("execute an interaction with Optional set to empty when its ingredient is provided") { context =>
      val ingredientValue: Optional[String] = java.util.Optional.of("optionalWithValue")

      val recipe =
        Recipe("IngredientProvidedRecipeWithEmptyOptionals")
          .withInteraction(
            interactionWithOptionalIngredients
              .withPredefinedIngredients(("missingJavaOptional", ingredientValue)))
          .withSensoryEvent(initialEvent)

      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, _) = bakerAndRecipeId

        compiledRecipe = RecipeCompiler.compileRecipe(recipe)
        recipeId <- baker.addRecipe(RecipeRecord.of(compiledRecipe))

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

    test("execute an interaction when its ingredient is provided and the interaction is renamed") { context =>
      val recipe =
        Recipe("IngredientProvidedRecipeWithRename")
          .withInteraction(interactionOne.withName("interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

      for {
        bakerAndRecipeId<- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerAndRecipeId
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    test("execute an interaction when both ingredients are provided (JOIN situation)") { context =>
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

    test("execute an interaction when two events occur (JOIN situation)") { context =>
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

    test("execute an interaction when one of the two events occur (OR situation)") { context =>
      val recipe = Recipe("ORPreconditionedRecipeForEvents")
        .withInteractions(interactionFour
          .withRequiredOneOfEvents(initialEvent, secondEvent))
        .withSensoryEvents(initialEvent, secondEvent)

      for {
        bakerAndRecipeId<- context.setupBakerWithRecipe(recipe,  mockImplementations)
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

    test("execute an interaction when one of the two events occur with two OR conditions (OR situation 2)") { context =>
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
          timer.sleep(600.millis).to[F]
            .as(InteractionOneSuccessful(interactionOneIngredientValue))
        })
        _ = when(testInteractionTwoMock.apply(anyString()))
          .thenAnswer((_: InvocationOnMock) => {
              timer.sleep(600.millis).unsafeRunSync()
              EventFromInteractionTwo(interactionTwoIngredientValue)
          })
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        start <- timer.clock.realTime(MILLISECONDS).to[F]
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        finish <- timer.clock.realTime(MILLISECONDS).to[F]
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
        _ = when(testInteractionOneMock.apply(recipeInstanceId.toString, firstData)).thenReturn(effect.pure(InteractionOneSuccessful(firstResponse)))
        _ = when(testInteractionOneMock.apply(recipeInstanceId.toString, secondData)).thenReturn(effect.pure(InteractionOneSuccessful(secondResponse)))
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
        .thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))

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

  }
}
