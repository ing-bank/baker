package com.ing.baker.compiler

import com.ing.baker._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.scaladsl.{InteractionDescriptorFactory, Recipe}

import scala.concurrent.duration._
import scala.language.postfixOps

import TestRecipeHelper._

class RecipeCompilerSpec extends TestRecipeHelper {


  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  "The RecipeCompiler after compilation" should {

    "should not contain errors if compiling a valid recipe" in {
      val recipe: Recipe = getComplexRecipe("ValidRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      System.out.println(compiledRecipe.getRecipeVisualization)
      //For now all missing implementation errors are provided so they are filtered out
      compiledRecipe.validationErrors.filterNot(s => s.startsWith("No implementation provided for interaction")) shouldBe List.empty
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
  }
}
