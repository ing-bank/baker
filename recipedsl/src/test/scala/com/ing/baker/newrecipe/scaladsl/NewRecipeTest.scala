package com.ing.baker.newrecipe.scaladsl

import org.scalatest.mock.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}

object NewRecipeTest {
  //Ingredients
  val customerName = Ingredient[String]("customerName")
  val customerId = Ingredient[String]("customerId")
  val accountId = Ingredient[Int]("accountId")

  //Events
  val AgreementsAccepted = Event("AgreementsAccepted")
  val NameProvided = Event("NameProvided", Seq(customerName))
  val AccountOpened = Event("AccountOpened", Seq(accountId))
  val AccountOpenedFailed = Event("AccountOpenedFailed")

  //Interactions
  val CreateCustomer = Interaction(
    name = "CreateCustomer",
    inputIngredients = Seq(customerName),
    interactionOutput = ProvidesIngredient(customerId)
  )

  val OpenAccount = Interaction(
    name = "OpenAccount",
    inputIngredients = Seq(customerId),
    interactionOutput = FiresOneOfEvents(AccountOpened, AccountOpenedFailed)
  )

  //Recipe
  val OnboardingRecipe =
  Recipe("OnboardingRecipe")
    .withInteractions(
      CreateCustomer,
      OpenAccount)
    .withSensoryEvents(
      AgreementsAccepted
    )
}

class NewRecipeTest extends WordSpecLike with Matchers with MockitoSugar {
  "compile for the old recipe dsl" in {
  }
}

