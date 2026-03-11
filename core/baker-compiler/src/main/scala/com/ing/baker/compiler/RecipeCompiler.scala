package com.ing.baker
package compiler

import com.ing.baker.il.{CompiledRecipe, ValidationSettings}
import com.ing.baker.recipe.common._

import scala.language.postfixOps

object RecipeCompiler {

  def compileRecipe(recipe: Recipe): CompiledRecipe =
    compileRecipe(recipe, ValidationSettings.defaultValidationSettings)

  def compileRecipe(recipe: Recipe, validationSettings: ValidationSettings): CompiledRecipe =
    RecipeCompilerScala.compileRecipe(recipe, validationSettings)
}
