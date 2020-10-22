package com.ing.baker.runtime.model

import com.ing.baker.il.CompiledRecipe

trait RecipeManager[F[_]] {

  def addRecipe(compiledRecipe: CompiledRecipe): F[String]

  def getRecipe(recipeId: String): F[Option[(CompiledRecipe, Long)]]

  def getAllRecipes: F[Map[String, (CompiledRecipe, Long)]]
}
