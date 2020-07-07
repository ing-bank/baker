package com.ing.baker.runtime.model

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.BakerException.NoSuchRecipeException
import com.ing.baker.runtime.scaladsl.RecipeInformation

trait RecipeManager[F[_]] {

  def addRecipe(compiledRecipe: CompiledRecipe): F[String]

  def getRecipe(recipeId: String): F[Either[NoSuchRecipeException, RecipeInformation]]

  def getAllRecipes: F[Map[String, RecipeInformation]]
}
