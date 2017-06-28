package com.ing.baker.recipe.scaladsl

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient}
import com.ing.baker.recipe.scaladsl.ScaladslSpec._
import org.scalatest.mock.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}

object ScaladslSpec {
  //Ingredients
  val customerName = Ingredient[String]("customerName")
  val customerId = Ingredient[String]("customerId")
  val accountId = Ingredient[Int]("accountId")
  val accountName = Ingredient[Int]("accountName")

  //Events
  val agreementsAcceptedEvent = Event("agreementsAccepted")
  val manualApprovedEvent = Event("manualApproved")
  val automaticApprovedEvent = Event("automaticApproved")
  val NameProvidedEvent = Event("nameProvided", customerName)
  val accountOpenedEvent = Event("accountOpened", accountId, accountName)
  val accountOpenedFailedEvent = Event("accountOpenedFailed")

  //Recipe
  //Interactions
  val createCustomer = Interaction(
    name = "CreateCustomer",
    inputIngredients = customerName,
    output = ProvidesIngredient(customerId)
  )

  val openAccount = Interaction(
    name = "OpenAccount",
    inputIngredients =Seq(customerId),
    output = FiresOneOfEvents(Seq(accountOpenedEvent, accountOpenedFailedEvent)))

  val onboardingRecipe: Recipe =
    Recipe("newCustomerRecipe")
      .withInteractions(
        createCustomer
          .withRequiredEvent(
            agreementsAcceptedEvent)
          .withRequiredOneOfEvents(
            automaticApprovedEvent,
            manualApprovedEvent),
        openAccount
              .withEventOutputTransformer(
                accountOpenedEvent,
                "newAccountOpenedEvent",
                Map.empty)
      )
      .withSensoryEvents(
        agreementsAcceptedEvent,
        NameProvidedEvent,
        manualApprovedEvent,
        automaticApprovedEvent
      )
}

class ScaladslSpec extends WordSpecLike with Matchers with MockitoSugar {
  "an Recipe" when {
    "visualise the new customer recipe" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(onboardingRecipe)
      compiledRecipe.validationErrors shouldBe empty
      compiledRecipe.getRecipeVisualization should not be empty
//      println(compiledRecipe.getRecipeVisualization)
    }

    "visualise the new customer recipe petri net" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(onboardingRecipe)
      compiledRecipe.validationErrors shouldBe empty
      compiledRecipe.getPetriNetVisualization should not be empty
//      println(compiledRecipe.getPetriNetVisualization)
    }
  }
}


