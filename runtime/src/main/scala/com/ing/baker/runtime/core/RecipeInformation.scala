package com.ing.baker.runtime.core

import com.ing.baker.il.CompiledRecipe

case class RecipeInformation(recipeId: String, compiledRecipe: CompiledRecipe, recipeCreatedTime: Long, errors: Set[String]) {
}