package com.ing.recipe

import java.util.UUID

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe, _}
import org.scalatest.mock.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}

object ScaladslSpec {
  //Ingredients
  val processId = Ingredient[UUID]("ProcessId")
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


  val onboardingRecipe =
    Recipe("newCustomerRecipe")
      .withInteractions(
        createCustomer
          .withRequiredEvent(agreementsAcceptedEvent)
          .withRequiredOneOfEvents(automaticApprovedEvent, manualApprovedEvent),
        openAccount
          .withEventOutputTransformer(accountOpenedEvent, renameEvent))
      .withSensoryEvents(agreementsAcceptedEvent, NameProvidedEvent, manualApprovedEvent, automaticApprovedEvent)

  val onboardingRecipe2: Recipe =
    "newCustomerRecipe"
      .withInteractions(
        createCustomer
          .withRequiredEvent(agreementsAcceptedEvent)
          .withRequiredOneOfEvents(automaticApprovedEvent, manualApprovedEvent),
        openAccount
            .withEventOutputTransformer(accountOpenedEvent, renameEvent))
      .withSensoryEvents(agreementsAcceptedEvent, NameProvidedEvent, manualApprovedEvent, automaticApprovedEvent)

  def renameEvent(e: common.Event): common.Event = Event(e.name + "new", e.providedIngredients)

  //  val fn = (String, String): String
  //  Map("InteractionExample" -> fn)
}

class ScaladslSpec extends WordSpecLike with Matchers with MockitoSugar {
  import com.ing.recipe.ScaladslSpec._
  "an Recipe" when {
    "visualise the newCustomer recipe" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(onboardingRecipe)
      compiledRecipe.validationErrors shouldBe empty
      println(compiledRecipe.getRecipeVisualization)
    }

    "should be the same if directly calling the constructor or using the implicit from String" in {
      onboardingRecipe shouldBe onboardingRecipe2
    }
  }
}


