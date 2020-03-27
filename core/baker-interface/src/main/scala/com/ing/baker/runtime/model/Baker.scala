package com.ing.baker.runtime.model

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, RecipeInformation, SensoryEventResult}

trait Baker[F[_]] {

  def addRecipe(compiledRecipe: CompiledRecipe): F[String]

  def getRecipe(recipeId: String): F[RecipeInformation]

  def getAllRecipes: F[Map[String, RecipeInformation]]

  def addInteractionInstance(implementation: InteractionInstance): F[Unit]

  def bake(recipeId: String, recipeInstanceId: String): F[Unit]

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): F[SensoryEventResult]
}

