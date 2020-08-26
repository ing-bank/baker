package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

case class RecipeEventMetadata(recipeId: String, recipeName: String, recipeInstanceId: String) extends common.RecipeEventMetadata with JavaApi {

  def getRecipeId: String = recipeId

  def getRecipeName: String = recipeName

  def getRecipeInstanceId: String = recipeInstanceId

  def asScala: scaladsl.RecipeEventMetadata =
    scaladsl.RecipeEventMetadata(
      recipeId = recipeId,
      recipeName = recipeName,
      recipeInstanceId = recipeInstanceId
    )
}
