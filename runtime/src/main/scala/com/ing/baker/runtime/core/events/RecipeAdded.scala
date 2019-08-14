package com.ing.baker.runtime.core.events

import com.ing.baker.il.CompiledRecipe

/**
  * An event describing the fact that a recipe was added to baker.
  *
  * @param recipeName The name of the recipe
  * @param recipeId The id of the recipe
  * @param date The time the recipe was added to baker
  */
case class RecipeAdded(recipeName: String,
                       recipeId: String,
                       date: Long,
                       compiledRecipe: CompiledRecipe) extends BakerEvent
