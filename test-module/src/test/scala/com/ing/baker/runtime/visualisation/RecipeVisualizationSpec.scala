package com.ing.baker.runtime.visualisation

import com.ing.baker.TestRecipeHelper
import com.ing.baker.il.{CompiledRecipe, RecipeVisualizer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe

import scala.concurrent.duration._
import scala.language.postfixOps

class RecipeVisualizationSpec extends TestRecipeHelper {

  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  override def afterAll {
    defaultActorSystem.terminate()
  }

  "The Recipe visualisation module" should {

    "be able to visualize a a created compile recipe" in {
      val recipe: Recipe = getComplexRecipe("VisiualizationRecipe")
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe)
      dot should include("interactionOneIngredient -> InteractionThree")
    }

    "be able to visualize the created interactions with a filter" in {
      val recipe: Recipe = getComplexRecipe("filteredVisualRecipe")
      val compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      val dot: String = RecipeVisualizer.visualiseCompiledRecipe(compileRecipe, filter = e => !e.contains("interactionFour"))
      dot shouldNot contain("interactionFour")
    }
  }
}
