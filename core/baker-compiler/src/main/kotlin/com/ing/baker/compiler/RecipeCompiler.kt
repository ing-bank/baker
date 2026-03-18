package com.ing.baker.compiler

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.ValidationSettings
import com.ing.baker.recipe.common.Recipe

object RecipeCompiler {

    /**
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @return
     */
    fun compileRecipe(recipe: Recipe): CompiledRecipe =
        compileRecipe(recipe, ValidationSettings.defaultValidationSettings())

    /**
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @param validationSettings The validation settings to follow for the validation
     * @return
     */
    fun compileRecipe(recipe: Recipe, validationSettings: ValidationSettings): CompiledRecipe =
        RecipeCompilerKotlin.compileRecipe(recipe, validationSettings)
}
