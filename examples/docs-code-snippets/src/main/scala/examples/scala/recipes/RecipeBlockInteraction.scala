package examples.scala.recipes

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe

object RecipeBlockInteraction {
  val recipe: Recipe = Recipe("example")
    .withDefaultFailureStrategy(
      InteractionFailureStrategy.BlockInteraction()
    )
}