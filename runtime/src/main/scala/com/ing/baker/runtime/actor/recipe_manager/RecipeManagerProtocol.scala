package com.ing.baker.runtime.actor.recipe_manager

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.BakerProtoMessage

object RecipeManagerProtocol {

  sealed trait RecipeManagerMessage extends BakerProtoMessage

  //Add a recipe
  case class AddRecipe(compiledRecipe: CompiledRecipe) extends RecipeManagerMessage

  case class AddRecipeResponse(recipeId: String) extends RecipeManagerMessage

  //Get a specific recipe
  case class GetRecipe(recipeId: String) extends RecipeManagerMessage

  case class RecipeFound(compiledRecipe: CompiledRecipe) extends RecipeManagerMessage

  case class NoRecipeFound(recipeId: String) extends RecipeManagerMessage

  //Get all recipes
  case object GetAllRecipes extends RecipeManagerMessage

  case class AllRecipes(compiledRecipes: Map[String, CompiledRecipe]) extends RecipeManagerMessage
}
