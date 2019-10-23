package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.javadsl

case class RecipeInstanceMetadata(recipeId: String, recipeInstanceId: String, createdTime: Long) extends com.ing.baker.runtime.common.RecipeInstanceMetadata with ScalaApi {

  def asJava: javadsl.RecipeInstanceMetadata =
    new javadsl.RecipeInstanceMetadata(recipeId, recipeInstanceId, createdTime)
}

