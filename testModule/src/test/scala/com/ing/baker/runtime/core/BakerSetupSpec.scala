package com.ing.baker.runtime.core

import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.core.{BakerException, NonSerializableException, RecipeValidationException}
import com.ing.baker.recipe.scaladsl.Recipe

import scala.concurrent.duration._
import scala.language.postfixOps

class BakerSetupSpec extends TestRecipeHelper {

  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  "The Baker execution engine during setup" should {

    "should startup correctly without throwing an error if provided a correct recipe and correct implementations" in {
      val recipe = getComplexRecipe("ValidRecipe")
      new Baker(
        compiledRecipe = RecipeCompiler.compileRecipe(recipe),
        implementations = mockImplementations,
        actorSystem = defaultActorSystem)
    }

    "throw an RecipeValidationException if an invalid recipe is given" in {
      val recipe = Recipe("NonProvidedIngredient")
        .withInteraction(interactionOne)

      a[RecipeValidationException] should be thrownBy {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      }
    }

    //Sieves are not auto constructed anymore, find out if we want this back or not
    "throw a BakerException if a sieve does not have a default constructor" ignore {
      val recipe = Recipe("SieveWithoutDefaultConstructor")
          .withInteractions(sieveInteractionWithoutDefaultConstructor)
          .withSensoryEvent(initialEvent)

      intercept[BakerException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Map.empty,
          actorSystem = defaultActorSystem)
      } should have('message("No default constructor found for Sieve: 'class com.ing.baker.SieveInteractionWithoutDefaultConstructor'"))
    }

    "throw an BakerException if a recipe does not provide an implementation for an interaction" in {
      val recipe = Recipe("MissingImplementation")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      intercept[BakerException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Map.empty,
          actorSystem = defaultActorSystem)
      } should have('message("No implementation provided for interaction: InteractionOne"))
    }

    "throw NonSerializableException with the list of ingredient serialization validation errors for Ingredients provided by Interactions" in {

      val recipe = Recipe("NonSerializableIngredientTest")
        .withInteraction(NonSerializableIngredientInteraction)
        .withSensoryEvent(initialEvent)

      intercept[NonSerializableException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      } should have('message("Ingredient nonSerializableIngredient of class com.ing.baker.NonSerializableObject is not serializable by akka"))

    }

    "throw NonSerializableException with the list of ingredient serialization validation errors for Ingredients provided by Events" in {

      val recipe = Recipe("NonSerializableIngredientFromEventTest")
          .withSensoryEvent(eventWithANonSerializableIngredient)

      intercept[NonSerializableException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      } should have('message("Ingredient nonSerializableIngredient of class com.ing.baker.NonSerializableObject is not serializable by akka"))

    }


    //Events are not know when Baker is startup, each event is transformed into a RuntimeEvent that is always Serializable.
    "throw NonSerializableException with a list of non serializable events if an event is not Serializable" ignore {

      val recipe = Recipe("NonSerializableEventTest")
        .withInteraction(NonSerializableEventInteraction)
        .withSensoryEvent(initialEvent)

      intercept[NonSerializableException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      } should have('message("Event class: class com.ing.baker.NonSerializableObject does not extend from com.ing.baker.api.Event"))
    }

  }
}
