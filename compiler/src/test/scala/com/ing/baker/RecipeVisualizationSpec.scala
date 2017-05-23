package com.ing.baker

import java.util.UUID

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.SRecipe

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

  "The CompiledRecipe" should {

    "be able to visualize the created interactions" in {
      val recipe: SRecipe = getComplexRecipe("VisiualizationRecipe")
      val compileRecipe = RecipeCompiler.compileRecipe(recipe)
      compileRecipe.getRecipeVisualization should include(
        "interactionOneIngredient -> InteractionThree")

      // Write visual recipe to a file so we can convert it to PNG easily
      // Online tool to use: http://mdaines.github.io/viz.js/
      // File("TestRecipe.dot").printlnAll(baker.recipe.getRecipeVisualization)

      // just to get an idea of how it looks like and to visualize it here: http://www.webgraphviz.com/
      // println(baker.recipe.getRecipeVisualization)
    }

    "be able to visualize the created interactions with a filter" in {
      RecipeCompiler.compileRecipe(getComplexRecipe("filteredVisualRecipe")).getFilteredRecipeVisualization(e => !e.contains("interactionFour")) shouldNot contain("interactionFour")
    }
  }
}
