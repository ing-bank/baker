package com.ing.baker.recipe.scaladsl

import org.scalatest.{Matchers, WordSpecLike}

class CommonMacrosSpec extends WordSpecLike with Matchers {

  "an Ingredient" when {
    "constructed using macro" should {
      "correctly derive the class and the name" in {
        val myIngredient = Ingredient[String]
        myIngredient.clazz shouldBe classOf[String]
        myIngredient.name shouldBe "myIngredient"
      }
    }
  }

  "an Event" when {
    "constructed using macro" should {

      "correctly derive the name" in {
        val myEvent = Event()
        myEvent.name shouldBe "myEvent"
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
}
