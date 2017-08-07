package com.ing.baker

import com.ing.baker.compiler.RecipeCompiler

class ExamplesSpec extends TestRecipeHelper {
  override def actorSystemName = "ExamplesSpec"

  "An example web-shop recipe" ignore {
    "be represented in a DOT format that is suitable for visualization" should {
      println(RecipeCompiler.compileRecipe(getWebshopRecipe).getRecipeVisualization)
    }
  }
}
