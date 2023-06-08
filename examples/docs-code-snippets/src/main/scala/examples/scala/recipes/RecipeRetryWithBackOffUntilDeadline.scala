package examples.scala.recipes

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl.Recipe

import scala.concurrent.duration.DurationInt

object RecipeRetryWithBackOffUntilDeadline {
  val recipe: Recipe = Recipe("example")
    .withDefaultFailureStrategy(
      RetryWithIncrementalBackoff
        .builder()
        .withInitialDelay(100.milliseconds)
        .withBackoffFactor(2.0)
        .withMaxTimeBetweenRetries(Some(10.minutes))
        .withUntil(Some(UntilDeadline(24.hours)))
        .build()
    )
}