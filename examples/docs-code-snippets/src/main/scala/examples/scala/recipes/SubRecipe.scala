package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe

object SubRecipe {
  val recipe: Recipe = Recipe("root recipe")
    .withSubRecipe(Recipe("sub recipe 1"))
    .withSubRecipe(Recipe("sub recipe 2")
      .withSubRecipe(Recipe("sub sub recipe 2.1"))
    )
}