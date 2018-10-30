package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common.ProvidesNothing
import org.scalatest.{Matchers, WordSpecLike}


class InteractionSpec extends WordSpecLike with Matchers {
  "an Interaction" when {
    "calling the Equals method" should {
      "return true if same interaction instance" in {
        val customerName = Ingredient[String]("customerName")
        val createCustomer = Interaction(
          name = "CreateCustomer",
          inputIngredients = Seq(customerName),
          output = ProvidesNothing
        )
        createCustomer.equals(createCustomer) shouldBe true
      }

      "return true if different interaction instance with same signature" in {
        val customerName = Ingredient[String]("customerName")
        val customerId = Ingredient[String]("customerId")
        val CreateCustomer = Interaction(
          name = "CreateCustomer",
          inputIngredients = Seq(customerName),
          output = ProvidesNothing
        )
        val CreateCustomer2 = Interaction(
          name = "CreateCustomer",
          inputIngredients = Seq(customerName),
          output = ProvidesNothing
        )
        CreateCustomer.equals(CreateCustomer2) shouldBe true
      }

      "return false if different interaction instance with different name" in {
        val customerName = Ingredient[String]("customerName")
        val customerId = Ingredient[String]("customerId")
        val CreateCustomer = Interaction(
          name = "CreateCustomer",
          inputIngredients = Seq(customerName),
          output = ProvidesNothing
        )
        val CreateCustomer2 = Interaction(
          name = "CreateCustomer2",
          inputIngredients = Seq(customerName),
          output = ProvidesNothing
        )
        CreateCustomer.equals(CreateCustomer2) shouldBe false
      }

      "return false if different object" in {
        val customerName = Ingredient[String]("customerName")
        val customerId = Ingredient[String]("customerId")
        val CreateCustomer = Interaction(
          name = "CreateCustomer",
          inputIngredients = Seq(customerName),
          output = ProvidesNothing
        )
        val otherObject = ""
        CreateCustomer.equals(otherObject) shouldBe false
      }
    }
  }
}
