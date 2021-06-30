package com.ing.baker.runtime.common

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait RecipeInformation extends LanguageApi {

  val compiledRecipe: CompiledRecipe

  val recipeCreatedTime: Long

  val validate: Boolean

  val errors: language.Set[String]

}
