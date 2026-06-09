package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}

case class RecipeInstanceMetadata(recipeId: String, recipeInstanceId: String, createdTime: Long) extends common.RecipeInstanceMetadata with ScalaApi {

  def asJava: javadsl.RecipeInstanceMetadata =
    javadsl.RecipeInstanceMetadata(recipeId, recipeInstanceId, createdTime)
}

