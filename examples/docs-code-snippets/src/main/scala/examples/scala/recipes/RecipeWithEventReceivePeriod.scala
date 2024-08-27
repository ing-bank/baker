package examples.scala.recipes

import com.ing.baker.recipe.scaladsl.Recipe

import scala.concurrent.duration.{FiniteDuration, HOURS}

object RecipeWithEventReceivePeriod {
  val recipe: Recipe = Recipe(name = "example")
    .withEventReceivePeriod(FiniteDuration.apply(5, HOURS))
}