package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import kotlin.time.Duration.Companion.hours

@ExperimentalDsl
object RecipeWithEventReceivePeriod {
    val recipe = recipe(name = "example") {
        eventReceivePeriod = 5.hours
    }
}