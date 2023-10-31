package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe

import scala.concurrent.duration.{DAYS, FiniteDuration, HOURS}

object RecipeWithRetentionPeriod {
  val recipe: Recipe = Recipe(name = "example")
    .withRetentionPeriod(FiniteDuration.apply(3, DAYS))
}