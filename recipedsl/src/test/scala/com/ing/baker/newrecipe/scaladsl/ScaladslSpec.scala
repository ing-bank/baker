package com.ing.baker.newrecipe.scaladsl

import org.scalatest.mock.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}
import com.ing.baker.newrecipe.scaladsl.ScaladslSpec._

object ScaladslSpec {
  //Ingredients
  val customerName = Ingredient[String]("customerName")
  val customerId = Ingredient[String]("customerId")
  val accountId = Ingredient[Int]("accountId")
  val accountName = Ingredient[Int]("accountName")

  //Events
  val AgreementsAcceptedEvent = Event("AgreementsAccepted")
  val NameProvidedEvent = Event("NameProvided", customerName)
  val AccountOpenedEvent = Event("AccountOpened", accountId, accountName)
  val AccountOpenedFailedEvent = Event("AccountOpenedFailed")

  //Recipe
  //Interactions
  val CreateCustomer = Interaction(
    name = "CreateCustomer",
    inputIngredients = customerName,
    interactionOutput = ProvidesIngredient(customerId)
  )

  val OpenAccount = Interaction(
    name = "OpenAccount",
    inputIngredients = customerId,
    interactionOutput = FiresOneOfEvents(Seq(AccountOpenedEvent, AccountOpenedFailedEvent))
  )

  val onboardingRecipe =
    Recipe("newCustomer")
      .withInteractions(
        CreateCustomer
          .withRequiredEvent(AgreementsAcceptedEvent),
        OpenAccount)
      .withSensoryEvent(
        AgreementsAcceptedEvent
      )

}

class ScaladslSpec extends WordSpecLike with Matchers with MockitoSugar {
  "an Recipe" when {

    "calling the toString method" should {
      "visualise the simplest recipe" in {
        val simpleRecipe = Recipe("SimpleRecipe")
        simpleRecipe.toString shouldNot equal("")
      }


      "visualise the complexer recipe" in {
        onboardingRecipe.toString
      }
    }
  }
}

