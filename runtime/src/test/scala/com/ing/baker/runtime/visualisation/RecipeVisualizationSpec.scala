package com.ing.baker.runtime.visualisation

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.{CompiledRecipe, RecipeVisualizer}
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.scaladsl.{Recipe, _}
import org.scalatest.{Matchers, WordSpecLike}

import scala.language.postfixOps

class RecipeVisualizationSpec extends WordSpecLike with Matchers {

  "The Recipe visualisation module" should {

    "be able to visualize a a created compile recipe" in {
      val recipe: Recipe = getRecipe("VisualizationRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compiledRecipe)
      dot should include("interactionOneIngredient -> InteractionThree")

//      baker.dumpToFile("TestRecipe.svg", compiledRecipe.getVisualRecipeAsSVG)
    }

    "be able to visualize the created interactions with a filter" in {
      val recipe: Recipe = getRecipe("filteredVisualRecipe")
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe, filter = e => !e.contains("interactionFour"))
      dot shouldNot contain("interactionFour")
    }

    "should visualize missing events with a red color" in {
      val recipe: Recipe = Recipe("missingEvent")
        .withInteraction(interactionOne.withRequiredEvent(secondEvent))
        .withSensoryEvent(initialEvent)
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe)
      dot should include("#EE0000")
    }

    "should visualize missing ingredients with a red color" in {
      val recipe: Recipe = Recipe("missingEvent")
        .withInteraction(interactionOne)
        .withSensoryEvent(secondEvent)
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe)
      dot should include("#EE0000")
    }
  }
}
