package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours

@ExperimentalDsl
object RecipeWithRetentionPeriod {
    val recipe = recipe(name = "example") {
        retentionPeriod = 3.days
    }
}