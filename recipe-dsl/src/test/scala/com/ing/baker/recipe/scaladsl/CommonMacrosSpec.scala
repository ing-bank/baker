package com.ing.baker.recipe.scaladsl

import org.scalatest.{Matchers, WordSpecLike}

class CommonMacrosSpec extends WordSpecLike with Matchers {

  "an Ingredient" when {
    "constructed using macro" should {
      "correctly derive the class and the name" in {
        val myIngredient = ngredient[String]
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
    }
  }
}
