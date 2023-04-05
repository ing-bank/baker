package com.ing.baker.runtime.model

import cats.effect.ConcurrentEffect
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.{CheckPointEvent, Recipe}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.ScalaDSLRuntime._
import org.mockito.ArgumentMatchers._
import org.mockito.Mockito._

import scala.annotation.nowarn
import scala.reflect.ClassTag
import cats.implicits._
import com.ing.baker.recipe.TestRecipe.InteractionOneSuccessful
import com.ing.baker.runtime.scaladsl.EventInstance

import java.util.UUID
import scala.concurrent.Future

@nowarn
trait BakerModelSpecSetupTests[F[_]] {
  self: BakerModelSpec[F] =>

  def runSetupTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {

    test("correctly load extensions when specified in the configuration") { context =>
      val simpleRecipe = RecipeCompiler.compileRecipe(Recipe("SimpleRecipe")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent))

      for {
        baker <- context.setupBakerWithNoRecipe(mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful("foobar")))
        recipeId <- baker.addRecipe(RecipeRecord.of(simpleRecipe))
        recipeInstanceId = java.util.UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, initialEvent.instance("initialIngredient"))
      } yield succeed
    }

    test("providing implementations in a sequence") { context =>
      for {
        baker <- context.setupBakerWithNoRecipe(mockImplementations)
      } yield succeed
    }

    test("providing an implementation with the class simplename same as the interaction") { context =>
      for {
        baker <- context.setupBakerWithNoRecipe(mockImplementations)
      } yield succeed
    }

    test("providing an implementation for a renamed interaction") { context =>
      val recipe = Recipe("simpleNameImplementationWithRename")
        .withInteraction(interactionOne.withName("interactionOneRenamed"))
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.setupBakerWithNoRecipe(List(InteractionInstance.unsafeFrom(new InteractionOneSimple())))
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      } yield succeed
    }

    test("providing an implementation with a name field") { context =>
      val recipe = Recipe("fieldNameImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.setupBakerWithNoRecipe(List((InteractionInstance.unsafeFrom(new InteractionOneFieldName()))))
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      } yield succeed
    }

    test("providing the implementation in a sequence with the interface its implementing with the correct name") { context =>

      val recipe = Recipe("interfaceImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.buildBaker(List(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      } yield succeed
    }

    test("the recipe contains complex ingredients that are serializable") { context =>
      val recipe = Recipe("complexIngredientInteractionRecipe")
        .withInteraction(interactionWithAComplexIngredient)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.buildBaker(List(InteractionInstance.unsafeFrom(mock[ComplexIngredientInteraction])))
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      } yield succeed
    }

    test("throw a exception when an invalid recipe is given") { context =>

      val recipe = Recipe("NonProvidedIngredient")
        .withInteraction(interactionOne)
        .withSensoryEvent(secondEvent)

      for {
        baker <- context.buildBaker(mockImplementations)
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe))).attempt.map {
          case Left(e) => e should have('message("Recipe NonProvidedIngredient:68b775e508fc6877 has validation errors: Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction"))
          case Right(_) => fail("Adding a recipe should fail")
        }
      } yield succeed
    }

    test("throw a exception when a recipe does not provide an implementation for an interaction") { context =>

      val recipe = Recipe("MissingImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      for {
        baker <- context.buildBaker(List.empty)
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe))).attempt.map {
          case Left(e) => e should have('message("Recipe MissingImplementation:dc3970efc8837e64 has implementation errors: No compatible implementation provided for interaction: InteractionOne: List(NameNotFound)"))
          case Right(_) => fail("Adding a recipe should fail")
        }
      } yield succeed
    }

    test("throw a exception when a recipe provides an implementation for an interaction and does not comply to the Interaction") { context =>

      val recipe = Recipe("WrongImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      for {
        baker <- context.buildBaker(List(InteractionInstance.unsafeFrom(new InteractionOneWrongApply())))
        _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe))).attempt.map {
          case Left(e) => e should have('message("Recipe WrongImplementation:8e2745de0bb0bde5 has implementation errors: No compatible implementation provided for interaction: InteractionOne: List(InteractionOne input size differs: transition expects 2, implementation provides 1)"))
          case Right(_) => fail("Adding an interaction should fail")
        }
      } yield succeed
    }

    test("run recipe with checkpointevent") { context =>

      val recipe = Recipe("CheckpointEvent")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
          .withCheckpointEvent(CheckPointEvent("Success")
          .withRequiredEvents(initialEvent)
          .withRequiredEvents(interactionOneSuccessful))


      val compiled = RecipeCompiler.compileRecipe(recipe)

      for {
        baker <- context.buildBaker(List(InteractionInstance.unsafeFrom(testInteractionOneMock)))
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful("Hello")))
        _ <- baker.addRecipe(RecipeRecord.of(compiled))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(compiled.recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> "Hello")
        _ = state.eventNames shouldBe Seq("InitialEvent", "InteractionOneSuccessful", "Success")
      } yield succeed
    }
  }

}
