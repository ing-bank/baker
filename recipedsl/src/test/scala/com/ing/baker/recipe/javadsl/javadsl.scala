package com.ing.baker.newrecipe.javadsl


import com.ing.baker.recipe.annotations.{ProvidesIngredient, RequiresIngredient}
import com.ing.baker.recipe.javadsl.{Interaction, Recipe}
import org.scalatest.{Matchers, WordSpecLike}
import org.scalatest.mock.MockitoSugar

object javadsl {
  trait SimpleInteraction extends Interaction{
    @ProvidesIngredient("originalIngredient")
    def action1(@RequiresIngredient("overriddenName") arg1: String): Int
  }
}

class javadsl extends WordSpecLike with Matchers with MockitoSugar {
  "an recipe" when {
    "using the javadsl" should {
      "should be able to setup a simple recipe" in {
        val recipe: Recipe = new Recipe("SimpleRecipe")


      }
    }
  }

}
