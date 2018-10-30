package com.ing.baker.runtime.core

import com.ing.baker.il.CompiledRecipe

import scala.collection.JavaConverters._

case class RecipeInformation(compiledRecipe: CompiledRecipe, recipeCreatedTime: Long, errors: Set[String]) {

  def getRecipeId(): String = compiledRecipe.recipeId

  def getCompiledRecipe(): CompiledRecipe = compiledRecipe

  def getRecipeCreatedTime(): Long = recipeCreatedTime

  def getErrors(): java.util.Set[String] = errors.asJava
}