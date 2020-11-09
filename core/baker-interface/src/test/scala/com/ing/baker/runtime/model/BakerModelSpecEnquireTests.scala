package com.ing.baker.runtime.model

import cats.effect.ConcurrentEffect
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler

import scala.reflect.ClassTag

trait BakerModelSpecEnquireTests[F[_]] { self: BakerModelSpec[F] =>

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
}
