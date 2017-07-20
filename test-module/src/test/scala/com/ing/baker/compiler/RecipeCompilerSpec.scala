package com.ing.baker.compiler

import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common.ProvidesNothing
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

import scala.concurrent.duration._
import scala.language.postfixOps

class RecipeCompilerSpec extends TestRecipeHelper {


  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  "The RecipeCompiler" should {

    "not have validation errors for a valid recipe" in {
      val recipe: Recipe = getComplexRecipe("ValidRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
    }

    "give a List of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction" in {
      val recipe = Recipe("NonProvidedIngredient")
        .withInteractions(interactionOne)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction")
    }

    "give a list of wrong ingredients if an predefined ingredient is of the wrong type" in {
      val recipe = Recipe("WrongGivenIngredient")
        .withInteractions(
          interactionOne
            .withRequiredEvent(initialEvent)
            .withPredefinedIngredients(("initialIngredient", Integer.valueOf(12))))
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Predefined argument 'initialIngredient' is not of type: class java.lang.String on interaction: 'InteractionOne'")
    }

    "give a list of wrong ingredients if an predefined ingredient is not needed by the interaction" in {
      val recipe = Recipe("WrongGivenIngredient")
        .withInteractions(
          interactionOne
            .withPredefinedIngredients(("WrongIngredient", null)))
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Predefined argument 'WrongIngredient' is not defined on interaction: 'InteractionOne'")
    }

    "fail compilation for an empty or null named interaction" in {
      List("", null) foreach { name =>
        val invalidInteraction = Interaction(name, Seq.empty, ProvidesNothing)
        val recipe = Recipe("InteractionNameTest").withInteractions(invalidInteraction)

        intercept[IllegalArgumentException] {
          RecipeCompiler.compileRecipe(recipe)
        } getMessage() shouldBe "Interaction with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named sieve interaction" in {
      List("", null) foreach { name =>
        val invalidSieveInteraction = Interaction(name, Seq.empty, ProvidesNothing)
        val recipe = Recipe("SieveNameTest").withSieve(invalidSieveInteraction)

        intercept[IllegalArgumentException] {
          RecipeCompiler.compileRecipe(recipe)
        } getMessage() shouldBe "Sieve Interaction with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named event" in {
      List("", null) foreach { name =>
        val invalidEvent = Event(name)
        val recipe = Recipe("EventNameTest").withSensoryEvent(invalidEvent)

        intercept[IllegalArgumentException] {
          RecipeCompiler.compileRecipe(recipe)
        } getMessage() shouldBe "Event with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named ingredient" in {
      List("", null) foreach { name =>
        val invalidIngredient = Ingredient(name)
        val recipe = Recipe("IngredientNameTest").withSensoryEvent(Event("someEvent", invalidIngredient))

        intercept[IllegalArgumentException] {
          RecipeCompiler.compileRecipe(recipe)
        } getMessage() shouldBe "Ingredient with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named recipe" in {
      List("", null) foreach { name =>
        val recipe = Recipe(name)

        intercept[IllegalArgumentException] {
          RecipeCompiler.compileRecipe(recipe)
        } getMessage() shouldBe "Recipe with a null or empty name found"
      }
    }

  }
}
