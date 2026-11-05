package com.ing.baker.runtime.testkit

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe.getRecipe
import com.ing.baker.runtime.BakerRuntimeTestBase
import com.ing.baker.runtime.common.RecipeRecord
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike

trait BakerInquireSpecLike extends BakerRuntimeTestBase { this: AsyncWordSpecLike with Matchers =>

  "Baker" should {

    "return recipe if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnRecipe")
        recipe <- baker.getRecipe(recipeId)
      } yield recipe.compiledRecipe.name should startWith("returnRecipe")
    }

    "return all recipes if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnAllRecipes")
        recipeId2 <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2"))))
        recipes <- baker.getAllRecipes
        _ = recipes.size shouldBe 2
        _ = recipes(recipeId).compiledRecipe.name should startWith("returnAllRecipes")
        _ = recipes(recipeId2).compiledRecipe.name should startWith("returnAllRecipes2")
      } yield succeed
    }

    "return no errors of a recipe with no errors if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnHealthRecipe")
        recipeInformation <- baker.getRecipe(recipeId)
        _ = assert(recipeInformation.compiledRecipe.recipeId == recipeId && recipeInformation.errors.isEmpty)
      } yield succeed
    }

    "return no errors of all recipes if none contain errors if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnHealthAllRecipe")
        recipeId2 <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2"))))
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
