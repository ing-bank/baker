package com.ing.baker.runtime.baas

import com.ing.baker.il.CompiledRecipe

object BaaSProtocol {

  case class BaaSRemoteFailure(message: String)

  case class AddRecipeRequest(compiledRecipe: CompiledRecipe)

  case class AddRecipeResponse(recipeId: String)
}
