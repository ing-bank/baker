package examples.scala.recipes

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilMaximumRetries
import com.ing.baker.recipe.scaladsl.Recipe

import scala.concurrent.duration.DurationInt

object RecipeRetryWithBackOffUntilMaxRetries {
  val recipe: Recipe = Recipe("example")
    .withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100.milliseconds)
        .withBackoffFactor(2.0)
        .withMaxTimeBetweenRetries(Some(10.minutes))
        .withUntil(Some(UntilMaximumRetries(200)))
        .build()
    )
}