package examples.scala.recipes

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe

object RecipeFireEventAndResolve {
  val recipe: Recipe = Recipe("example")
    .withDefaultFailureStrategy(
      InteractionFailureStrategy.FireEventAndResolve(Some("MyEvent"))
    )
}