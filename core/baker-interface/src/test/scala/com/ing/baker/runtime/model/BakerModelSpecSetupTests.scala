package com.ing.baker.runtime.model

import cats.effect.{ConcurrentEffect, IO}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.model.ScalaDSLRuntime._
import com.ing.baker.runtime.scaladsl.InteractionInstanceF
import org.mockito.Matchers._
import org.mockito.Mockito._

import scala.concurrent.Future
import scala.reflect.ClassTag

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
        recipeId <- baker.addRecipe(simpleRecipe, System.currentTimeMillis())
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
        baker <- context.setupBakerWithNoRecipe(List(InteractionInstanceF.unsafeFrom(new InteractionOneSimple())))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), System.currentTimeMillis())
      } yield succeed
    }

    test("providing an implementation with a name field") { context =>
      val recipe = Recipe("fieldNameImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.setupBakerWithNoRecipe(List((InteractionInstanceF.unsafeFrom(new InteractionOneFieldName()))))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("providing the implementation in a sequence with the interface its implementing with the correct name") { context =>

      val recipe = Recipe("interfaceImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.buildBaker(List(InteractionInstanceF.unsafeFrom(new InteractionOneInterfaceImplementation())))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("the recipe contains complex ingredients that are serializable") { context =>
      val recipe = Recipe("complexIngredientInteractionRecipe")
        .withInteraction(interactionWithAComplexIngredient)
        .withSensoryEvent(initialEvent)
      for {
        baker <- context.buildBaker(List(InteractionInstanceF.unsafeFrom(mock[ComplexIngredientInteraction])))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield succeed
    }

    test("throw a exception when an invalid recipe is given") { context =>

      val recipe = Recipe("NonProvidedIngredient")
        .withInteraction(interactionOne)
        .withSensoryEvent(secondEvent)

      for {
        baker <- context.buildBaker(mockImplementations)
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
        baker <- context.buildBaker(List.empty)
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
        baker <- context.buildBaker(List(InteractionInstanceF.unsafeFrom(new InteractionOneWrongApply())))
        _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe)).attempt.map {
          case Left(e) => e should have('message("No implementation provided for interaction: InteractionOne"))
          case Right(_) => fail("Adding an interaction should fail")
        }
      } yield succeed
    }
  }

}
