package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.recipe.scaladsl.{Event, Ingredient}
import org.scalatest.{Matchers, WordSpecLike}
import org.scalatest.mock.MockitoSugar

class EventSpec extends WordSpecLike with Matchers with MockitoSugar {


  "an Event" when {

    "calling the Equals method" should {
      "return true if same event instance" in {
        val AgreementsAccepted = Event("AgreementsAccepted")
        AgreementsAccepted.equals(AgreementsAccepted) shouldBe true

        val customerName = Ingredient[String]("customerName")
        val NameProvided = Event("NameProvided", Seq(customerName))
        NameProvided.equals(NameProvided) shouldBe true
      }

      "return true if different event with same name and providedIngredients" in {
        val AgreementsAccepted = Event("AgreementsAccepted")
        val AgreementsAccepted2 = Event("AgreementsAccepted")
        AgreementsAccepted.equals(AgreementsAccepted2) shouldBe true

        val customerName = Ingredient[String]("customerName")
        val NameProvided = Event("NameProvided", Seq(customerName))
        val NameProvided2 = Event("NameProvided", Seq(customerName))
        NameProvided.equals(NameProvided2) shouldBe true
      }

      "return false if different event with different name" in {
        val AgreementsAccepted = Event("AgreementsAccepted")
        val AgreementsAccepted2 = Event("AgreementsAccepted2")
        AgreementsAccepted.equals(AgreementsAccepted2) shouldBe false
      }

      "return false if different event with same name and different ingredient" in {
        val customerName = Ingredient[String]("customerName")
        val customerName2 = Ingredient[String]("customerName2")
        val NameProvided = Event("NameProvided", Seq(customerName))
        val NameProvided2 = Event("NameProvided", Seq(customerName2))
        NameProvided.equals(NameProvided2) shouldBe false
      }

      "return false if different object" in {
        val AgreementsAccepted = Event("AgreementsAccepted")
        val otherObject = ""
        AgreementsAccepted.equals(otherObject) shouldBe false
      }
    }
  }
}
