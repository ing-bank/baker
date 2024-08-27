package examples.kotlin.visualization

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import examples.kotlin.recipes.WebShopRecipe

@ExperimentalDsl
fun printVisualizationString() {
    val compileRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe)
    val graphvizString = compileRecipe.recipeVisualization
    println(graphvizString)
}