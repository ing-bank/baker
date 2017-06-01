package com.ing.baker.newrecipe.scaladsl

import org.scalatest.mock.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}

class IngredientSpec extends WordSpecLike with Matchers with MockitoSugar {
  "an Ingredient" should {

    "be equal if they are the same object" in {
      val customerName = Ingredient[String]("customerName")
      customerName.equals(customerName) shouldBe true
    }

    "be equal if they are different object but have the same signatures" in {
      val customerName = Ingredient[String]("customerName")
      val customerName2 = Ingredient[String]("customerName")
      customerName.equals(customerName2) shouldBe true
    }

    "be not equal if they are different object and have different names" in {
      val customerName = Ingredient[String]("customerName")
      val agreementName = Ingredient[String]("agreementName")
      customerName.equals(agreementName) shouldBe false
    }

    "be not equal if they are different object and have different types" in {
      val customerName = Ingredient[String]("customerName")
      val customerName2 = Ingredient[Integer]("customerName")
      customerName.equals(customerName2) shouldBe false
    }
  }
}