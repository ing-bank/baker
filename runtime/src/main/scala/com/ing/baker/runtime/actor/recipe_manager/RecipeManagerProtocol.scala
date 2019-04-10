package com.ing.baker.runtime.actor.recipe_manager

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actortyped.serialization.BakerSerializable

sealed trait RecipeManagerProtocol extends BakerSerializable

object RecipeManagerProtocol {

  //Add a recipe
  case class AddRecipe(compiledRecipe: CompiledRecipe) extends RecipeManagerProtocol

  case class AddRecipeResponse(recipeId: String) extends RecipeManagerProtocol

  //Get a specific recipe
  case class GetRecipe(recipeId: String) extends RecipeManagerProtocol

  case class RecipeFound(compiledRecipe: CompiledRecipe, timestamp: Long) extends RecipeManagerProtocol

  case class NoRecipeFound(recipeId: String) extends RecipeManagerProtocol

  //Get all recipes
  case object GetAllRecipes extends RecipeManagerProtocol

  case class RecipeInformation(compiledRecipe: CompiledRecipe, timestamp: Long)

  case class AllRecipes(recipes: Seq[RecipeInformation]) extends RecipeManagerProtocol

}
