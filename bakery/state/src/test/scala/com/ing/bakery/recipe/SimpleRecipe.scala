package com.ing.bakery.recipe

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import com.ing.bakery.recipe.Events.OrderPlaced

import scala.concurrent.duration._


object SimpleRecipe {

  private def recipeBase = Recipe("Simple")
    .withSensoryEvents(
      Event[OrderPlaced])
    .withInteractions(
      Interactions.ReserveItemsInteraction)

  def recipe: Recipe =
    recipeBase.withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100.milliseconds)
        .withUntil(Some(UntilDeadline(24.hours)))
        .withMaxTimeBetweenRetries(Some(10.minutes))
        .build())

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)

}
