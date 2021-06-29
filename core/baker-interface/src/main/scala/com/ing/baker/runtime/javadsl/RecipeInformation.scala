package com.ing.baker.runtime.javadsl

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}

import scala.collection.JavaConverters._

case class RecipeInformation(compiledRecipe: CompiledRecipe,
                             recipeCreatedTime: Long,
                             errors: java.util.Set[String],
                             validate: Boolean) extends common.RecipeInformation with JavaApi {

  def getRecipeId: String = compiledRecipe.recipeId

  def getCompiledRecipe: CompiledRecipe = compiledRecipe

  def getRecipeCreatedTime: Long = recipeCreatedTime

  def getErrors: java.util.Set[String] = errors

  def asScala: scaladsl.RecipeInformation =
    scaladsl.RecipeInformation(compiledRecipe, recipeCreatedTime, errors.asScala.toSet, validate)
}

