package com.ing.baker.compiler

import java.util.Optional

import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.il.{CompiledRecipe, ValidationSettings}
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Ingredients, Interaction, Recipe}

import scala.language.postfixOps

class RecipeCompilerSpec extends TestRecipeHelper {

  override def actorSystemName = "RecipeCompilerSpec"

  before {
    resetMocks
  }

  "The RecipeCompiler should" should {

    "not have validation errors for a valid recipe" in {
      val recipe: Recipe = getComplexRecipe("ValidRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      println(compiledRecipe.getRecipeVisualization)
    }

    "give a List of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction" in {
      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(secondEvent)
        .withInteractions(interactionOne)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction")
    }

    "give an error if the processId is required and is not of the String type" in {
      val wrongProcessIdInteraction =
        Interaction("wrongProcessIdInteraction",
          Ingredients(new Ingredient[Int](common.ProcessIdName), initialIngredient),
          ProvidesIngredient(interactionOneOriginalIngredient))

      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(initialEvent)
        .withInteractions(wrongProcessIdInteraction)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Non supported process id class: int on interaction: 'wrongProcessIdInteraction'")
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

    "validate if there are unreachable interactions exist or not" in {
      val recipe = Recipe("RecipeWithUnreachableInteraction")
        .withInteractions(interactionSeven.withMaximumInteractionCount(1), interactionEight)
        .withSensoryEvent(initialEvent)

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe,
        ValidationSettings(allowNonExecutableInteractions = false))

      compiledRecipe.validationErrors should contain("InteractionEight is not executable")
    }

    "fail compilation for an empty or null named interaction" in {
      List("", null) foreach { name =>
        val invalidInteraction = Interaction(name, Seq.empty, ProvidesNothing)
        val recipe = Recipe("InteractionNameTest").withInteractions(invalidInteraction).withSensoryEvent(initialEvent)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Interaction with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named sieve interaction" in {
      List("", null) foreach { name =>
        val invalidSieveInteraction = Interaction(name, Seq.empty, ProvidesNothing)
        val recipe = Recipe("SieveNameTest").withSieve(invalidSieveInteraction).withSensoryEvent(initialEvent)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Sieve Interaction with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named event" in {
      List("", null) foreach { name =>
        val invalidEvent = Event(name)
        val recipe = Recipe("EventNameTest").withSensoryEvent(invalidEvent).withInteraction(interactionOne)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Event with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named ingredient" in {
      List("", null) foreach { name =>
        val invalidIngredient = Ingredient(name)
        val recipe = Recipe("IngredientNameTest").withSensoryEvent(Event("someEvent", invalidIngredient)).withInteraction(interactionOne)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Ingredient with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named recipe" in {
      List("", null) foreach { name =>
        val recipe = Recipe(name)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Recipe with a null or empty name found"
      }
    }

    "fail compilation for an empty/non-logical recipe" in {
      intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(Recipe("someName"))) getMessage() shouldBe "Not a valid recipe: No sensory events found."
      intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(Recipe("someName").withSensoryEvent(initialEvent))) getMessage() shouldBe "Not a valid recipe: No interactions or sieves found."
    }

    "interactions with optional ingredients that are not provided should be provided as empty" in {
      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(optionalIngredientInteraction)
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 4
            it.predefinedParameters("missingJavaOptional") shouldBe Optional.empty()
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })
    }

    "interactions with optional ingredients that are provided should not be provided as empty" in {
      val optionalProviderEvent = Event("optionalProviderEvent", missingJavaOptional)

      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(optionalIngredientInteraction)
        .withSensoryEvents(initialEvent, optionalProviderEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 3
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })
    }

    "interactions with optional ingredients that are predefined should not be provided as empty" in {
      val ingredientValue: Optional[String] = java.util.Optional.of("value")
      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(
          optionalIngredientInteraction
            .withPredefinedIngredients(("missingJavaOptional", ingredientValue))
        )
        .withSensoryEvents(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 4
            it.predefinedParameters("missingJavaOptional") shouldBe ingredientValue
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })
    }
  }
}
