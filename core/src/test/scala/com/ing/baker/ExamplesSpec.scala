package com.ing.baker

class ExamplesSpec extends TestRecipeHelper {
  "An example web-shop recipe" should {
    "be represented in a DOT format that is suitable for visualization" should {
      println(getWebshopRecipe.compileRecipe.getRecipeVisualization)
    }
  }
}
