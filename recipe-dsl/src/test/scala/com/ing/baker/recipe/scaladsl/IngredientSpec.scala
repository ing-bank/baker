package com.ing.baker.recipe.scaladsl

import com.ing.baker.types
import com.ing.baker.types._
import org.scalatest.{Matchers, WordSpecLike}

class IngredientSpec extends WordSpecLike with Matchers {
  "an Ingredient" when {

    "constructed" should {

      "correctly derive the type" in {

        val ingredient = Ingredient[String]("foo")
        ingredient.name shouldBe "foo"
        ingredient.ingredientType shouldBe types.CharArray
      }

      "correctly derive a higher kinded type" in {

        val ingredient = Ingredient[Option[String]]("foo")
        ingredient.name shouldBe "foo"
        ingredient.ingredientType shouldBe OptionType(types.CharArray)
      }
    }

    "calling the Equals method" should {

      "return true if same ingredient instance" in {
        val customerName = Ingredient[String]("customerName")
        customerName.equals(customerName) shouldBe true
      }

      "return true if different ingredient with same name and type" in {
        val customerName = Ingredient[String]("customerName")
        val customerName2 = Ingredient[String]("customerName")
        customerName.equals(customerName2) shouldBe true
      }

      "return false if different ingredient with different name and same type" in {
        val customerName = Ingredient[String]("customerName")
        val agreementName = Ingredient[String]("agreementName")
        customerName.equals(agreementName) shouldBe false
      }

      "return false if different ingredient with same name and different type" in {
        val customerName = Ingredient[String]("customerName")
        val customerName2 = Ingredient[Integer]("customerName")
        customerName.equals(customerName2) shouldBe false
      }

      "return false if different ingredient with different name and different type" in {
        val customerName = Ingredient[String]("customerName")
        val agreementName = Ingredient[Integer]("agreementName")
        customerName.equals(agreementName) shouldBe false
      }

      "return false if different object" in {
        val customerName = Ingredient[String]("customerName")
        val otherObject = ""
        customerName.equals(otherObject) shouldBe false
      }
    }
  }
}