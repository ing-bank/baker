package com.ing.baker.runtime.actor.recipe_manager

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.BakerProtoMessage

object RecipeManagerProtocol {
  //Add a recipe
  case class AddRecipe(compiledRecipe: CompiledRecipe) extends BakerProtoMessage

  case class AddRecipeResponse(recipeId: String) extends BakerProtoMessage

  //Get a specific recipe
  case class GetRecipe(recipeId: String) extends BakerProtoMessage

  case class RecipeFound(compiledRecipe: CompiledRecipe) extends BakerProtoMessage

  case class NoRecipeFound(recipeId: String) extends BakerProtoMessage

  //Get all recipes
  case object GetAllRecipes extends BakerProtoMessage

  case class AllRecipes(compiledRecipes: Map[String, CompiledRecipe]) extends BakerProtoMessage
}
