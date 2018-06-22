package com.ing.baker.runtime.visualisation

import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.TestRecipe._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.{CompiledRecipe, RecipeVisualizer}
import com.ing.baker.recipe.scaladsl.{Recipe, _}

import scala.language.postfixOps

class RecipeVisualizationSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "RecipeVisualizationSpec"

  before {
    resetMocks
  }

  "The Recipe visualisation module" should {

    "be able to visualize a a created compile recipe" in {
      val recipe: Recipe = getRecipe("VisiualizationRecipe")
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe)
      dot should include("interactionOneIngredient -> InteractionThree")
    }

    "be able to visualize the created interactions with a filter" in {
      val recipe: Recipe = getRecipe("filteredVisualRecipe")
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe, filter = e => !e.contains("interactionFour"))
      dot shouldNot contain("interactionFour")
    }

    "should visualize missing events with a red color" in {
      val recipe: Recipe = Recipe("misisngEvent")
        .withInteraction(interactionOne.withRequiredEvent(secondEvent))
        .withSensoryEvent(initialEvent)
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe)
      dot should include("#EE0000")
    }

    "should visualize missing ingredients with a red color" in {
      val recipe: Recipe = Recipe("misisngEvent")
        .withInteraction(interactionOne)
        .withSensoryEvent(secondEvent)
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe)
      dot should include("#EE0000")
    }
  }
}
