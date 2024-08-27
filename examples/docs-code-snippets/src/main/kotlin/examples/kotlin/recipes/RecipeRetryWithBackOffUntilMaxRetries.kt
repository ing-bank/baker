package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

@ExperimentalDsl
object RecipeRetryWithBackOffUntilMaxRetries {
    val recipe = recipe("example") {
        defaultFailureStrategy = retryWithIncrementalBackoff {
            initialDelay = 100.milliseconds
            backoffFactor = 2.0
            maxTimeBetweenRetries = 10.seconds
            until = maximumRetries(200)
        }
    }
}