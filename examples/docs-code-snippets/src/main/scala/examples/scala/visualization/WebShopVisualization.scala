package examples.scala.visualization

import com.ing.baker.compiler.RecipeCompiler
import examples.scala.recipes.WebShopRecipe

class WebShopVisualization {
  def printVisualizationString(): Unit = {
    val compiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe)
    val visualization = compiledRecipe.getRecipeVisualization
    println(visualization)
  }
}
