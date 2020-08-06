package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi

case class RecipeEventMetadata(recipeId: String, recipeName: String, recipeInstanceId: String) extends common.RecipeEventMetadata with ScalaApi {

  def asJava: javadsl.RecipeEventMetadata =
    javadsl.RecipeEventMetadata(
      recipeId = recipeId,
      recipeName = recipeName,
      recipeInstanceId = recipeInstanceId
    )
}
