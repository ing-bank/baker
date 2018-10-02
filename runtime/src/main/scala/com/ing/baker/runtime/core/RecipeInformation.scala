package com.ing.baker.runtime.core

import com.ing.baker.il.CompiledRecipe

import scala.collection.JavaConverters._

case class RecipeInformation(recipeId: String, compiledRecipe: CompiledRecipe, recipeCreatedTime: Long, errors: Set[String]) {

  def getRecipeId(): String = recipeId

  def getCompiledRecipe(): CompiledRecipe = compiledRecipe

  def getRecipeCreatedTime(): Long = recipeCreatedTime

  def getErrors(): java.util.Set[String] = errors.asJava
}