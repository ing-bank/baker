package examples.scala.recipes

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe

object RecipeFireEvent {
  val recipe: Recipe = Recipe("example")
    .withDefaultFailureStrategy(
      InteractionFailureStrategy.FireEventAfterFailure(Some("MyEvent"))
    )
}