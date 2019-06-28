package com.ing.baker.runtime.scaladsl

import com.ing.baker.il.CompiledRecipe

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common
import com.ing.baker.runtime.javadsl
import scala.collection.JavaConverters._

case class RecipeInformation(
                              compiledRecipe: CompiledRecipe,
                              recipeCreatedTime: Long,
                              errors: Set[String]) extends common.RecipeInformation with ScalaApi {

  def asJava: javadsl.RecipeInformation =
    new javadsl.RecipeInformation(compiledRecipe, recipeCreatedTime, errors.asJava)
}
