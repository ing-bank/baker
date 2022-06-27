package com.ing.baker.runtime.scaladsl

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}

import scala.annotation.nowarn
import scala.collection.JavaConverters._

case class EncodedRecipe(base64: String, createdAt: Long)

case class RecipeInformation(
                              compiledRecipe: CompiledRecipe,
                              recipeCreatedTime: Long,
                              errors: Set[String],
                              validate: Boolean) extends common.RecipeInformation with ScalaApi {

  @nowarn
  def asJava: javadsl.RecipeInformation =
    javadsl.RecipeInformation(compiledRecipe, recipeCreatedTime, errors.asJava, validate)
}
