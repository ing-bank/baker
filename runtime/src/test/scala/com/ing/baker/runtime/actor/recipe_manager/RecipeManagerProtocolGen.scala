package com.ing.baker.runtime.actor.recipe_manager

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.pbt.RecipePropertiesSpec.recipeGen
import org.scalacheck.Gen

object RecipeManagerProtocolGen {

  val addRecipe: Gen[RecipeManagerProtocol.AddRecipe] =
    for {
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManagerProtocol.AddRecipe(recipe)

  val addRecipeResponse: Gen[RecipeManagerProtocol.AddRecipeResponse] =
    for {
      recipeId <- Gen.alphaNumStr
    } yield RecipeManagerProtocol.AddRecipeResponse(recipeId)

  val getRecipe: Gen[RecipeManagerProtocol.GetRecipe] =
    for {
      recipeId <- Gen.alphaNumStr
    } yield RecipeManagerProtocol.GetRecipe(recipeId)

  val recipeFound: Gen[RecipeManagerProtocol.RecipeFound] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManagerProtocol.RecipeFound(recipe, timestamp)

  val noRecipeFound: Gen[RecipeManagerProtocol.NoRecipeFound] =
    for {
      recipeId <- Gen.alphaNumStr
    } yield RecipeManagerProtocol.NoRecipeFound(recipeId)

  val allRecipes: Gen[RecipeManagerProtocol.AllRecipes] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManagerProtocol.AllRecipes(Seq(RecipeManagerProtocol.RecipeInformation(recipe, timestamp)))

  val recipeAdded: Gen[RecipeManager.RecipeAdded] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManager.RecipeAdded(recipe, timestamp)
}
