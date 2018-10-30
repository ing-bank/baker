package com.ing.baker.recipe.scaladsl

import com.ing.baker.types
import org.scalatest.{Matchers, WordSpecLike}

class CommonMacrosSpec extends WordSpecLike with Matchers {

  "an Ingredient" when {
    "constructed using macro" should {
      "correctly derive the class and the name" in {
        val myIngredient = Ingredient[String]
        myIngredient.ingredientType shouldBe types.CharArray
        myIngredient.name shouldBe "myIngredient"
      }

      "do not derive the name if explicitly set" in {
        val myIngredient = Ingredient[String]("someIngredientName")
        myIngredient.ingredientType shouldBe types.CharArray
        myIngredient.name shouldBe "someIngredientName"
      }
    }
  }

  "an Event" when {
    "constructed using macro" should {

      "correctly derive the name" in {
        val myEvent = Event()
        myEvent.name shouldBe "myEvent"
      }

      "do not derive the name if explicitly set" in {
        val myEvent = Event("someEventName")
        myEvent.name shouldBe "someEventName"
      }

      "correctly derive the name when one ingredient is given" in {
        val ingr = Ingredient[String]
        val myEvent = Event(ingr)
        myEvent.name shouldBe "myEvent"
        myEvent.providedIngredients shouldBe Seq(ingr)
      }

      "correctly derive the name when two ingredients are given" in {
        val ingr1 = Ingredient[String]
        val ingr2 = Ingredient[String]
        val myEvent = Event(ingr1, ingr2)
        myEvent.name shouldBe "myEvent"
        myEvent.providedIngredients shouldBe Seq(ingr1, ingr2)
      }
    }
  }

  "a Recipe" when {
    "constructed using macro" should {

      "correctly derive the name" in {
        val myRecipe: Recipe = Recipe()
        myRecipe.name shouldBe "myRecipe"
      }

      "do not derive the name if explicitly set" in {
        val myRecipe = Recipe("recipeName")
        myRecipe.name shouldBe "recipeName"
      }
    }
  }
}
