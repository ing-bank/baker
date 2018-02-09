package com.ing.baker.runtime.actor.recipe_manager

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.InternalBakerMessage

object RecipeManagerProtocol {
  //Add a recipe
  case class AddRecipe(compiledRecipe: CompiledRecipe) extends InternalBakerMessage

  case class AddRecipeResponse(recipeId: String) extends InternalBakerMessage

  //Get a specific recipe
  case class GetRecipe(recipeId: String) extends InternalBakerMessage

  case class RecipeFound(compiledRecipe: CompiledRecipe) extends InternalBakerMessage

  case class NoRecipeFound(recipeId: String) extends InternalBakerMessage

  //Get alla recipe
  case object GetAllRecipes extends InternalBakerMessage

  case class AllRecipes(compiledRecipes: Map[String, CompiledRecipe]) extends InternalBakerMessage
}
