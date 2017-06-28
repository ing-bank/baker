package curryonexample

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.baker.recipe.scaladsl._
import org.scalatest.mock.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}
import newCustomerRecipeScala._

object newCustomerRecipeScala {
  //Ingredients
  val customerName = Ingredient[String]("customerName")
  val customerId = Ingredient[Int]("customerId")
  val accountName = Ingredient[String]("accountName")
  val accountId = Ingredient[Int]("accountId")
  val email = Ingredient[String]("email")

  //Sensory Events
  val customerDataProvided = Event("customerDataProvided", customerName, email)
  val agreementsAccepted = Event("agreementsAccepted")
  val manualApproved = Event("manualApproved")
  val automaticApproved = Event("automaticApproved")

  //Internal Event
  val accountOpened = Event("accountOpened", accountId, accountName)
  val accountOpeningFailed = Event("accountOpeningFailed")
  val messageSendToCustomer = Event("messageSendToCustomer")

  //Interactions
  val createCustomer = Interaction(
    name = "CreateCustomer",
    inputIngredients = customerName,
    output = ProvidesIngredient(customerId))

  val openAccount = Interaction(
    name = "OpenAccount",
    inputIngredients = customerId,
    output = FiresOneOfEvents(accountOpened, accountOpeningFailed))

  val sendSuccesMessageToCustomer = Interaction(
    name = "sendSuccesMessageToCustomer",
    inputIngredients = Ingredients(accountId, accountName, customerId ,customerName, email),
    output = FiresOneOfEvents(messageSendToCustomer))

  //Recipe
  val onboardingClientRecipe: Recipe =
    "newCustomerRecipe"
      .withInteractions(
        createCustomer
          .withRequiredEvent(
            agreementsAccepted)
          .withRequiredOneOfEvents(
            automaticApproved,
            manualApproved),
        openAccount,
        sendSuccesMessageToCustomer
      )
      .withSensoryEvents(
        customerDataProvided,
        agreementsAccepted,
        manualApproved,
        automaticApproved
      )
}

class newCustomerRecipeScala extends WordSpecLike with Matchers with MockitoSugar {
  "The new Customer Recipe" when {
    "created" should {
      "be printable" in {
//        println(onboardingClientRecipe)
      }
    }

    "compiled" should {
      val compiledRecipe = RecipeCompiler.compileRecipe(onboardingClientRecipe)
      "have no errors" in {
        compiledRecipe.validationErrors shouldBe empty
      }
      "be able to visualise the compiled recipe to a dot format" in {
//        println(compiledRecipe.getRecipeVisualization)
      }
      "be able to visualise the underlying perti net to a dot format" in {
//        println(compiledRecipe.getPetriNetVisualization)
      }
    }
  }
}
