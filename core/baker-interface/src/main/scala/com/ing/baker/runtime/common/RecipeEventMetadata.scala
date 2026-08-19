package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait RecipeEventMetadata extends LanguageApi {

  def recipeId: String

  def recipeName: String

  def recipeInstanceId: String

}
