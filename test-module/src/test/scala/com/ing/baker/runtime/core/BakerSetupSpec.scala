package com.ing.baker.runtime.core

import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.core.implementations.{InteractionOneFieldName, InteractionOneInterfaceImplementation, InteractionOneWrongApply}

import scala.language.postfixOps

class BakerSetupSpec extends TestRecipeHelper {

  override def actorSystemName = "BakerSetupSpec"

  before {
    resetMocks
  }

  "The Baker execution engine during setup" should {

    "bootstrap correctly without throwing an error if provided a correct recipe and correct implementations" when {

      "providing the implementation directly in a map" in {
        val recipe = Recipe("directImplementationmap")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations)
      }

      "providing the implementation in a sequence with the class simplename same as the interaction" in {
        val recipe = Recipe("simpleNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Seq(new implementations.InteractionOne()))
      }

      "providing the implementation in a sequence and interaction renamed" in {
        val recipe = Recipe("simpleNameImplementationWithRename")
          .withInteraction((interactionOne, "interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Seq(new implementations.InteractionOne()))
      }

      "providing the implementation in a sequence with the field name same as the interaction" in {
        val recipe = Recipe("fieldNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Seq(new InteractionOneFieldName()))
      }

      "providing the implementation in a sequence with the interface its implementing with the correct name" in {
        val recipe = Recipe("interfaceImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Seq(new InteractionOneInterfaceImplementation()))
      }

      "the recipe contains complex ingredients that are serializable" in {
        val recipe = Recipe("complexIngredientInteractionRecipe")
          .withInteraction(complexIngredientInteraction)
          .withSensoryEvent(initialEvent)

        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations)
      }
    }

    "throw a exception" when {
      "an invalid recipe is given" in {
        val recipe = Recipe("NonProvidedIngredient")
          .withInteraction(interactionOne)
          .withSensoryEvent(secondEvent)

        intercept[RecipeValidationException] {
          new Baker(
            compiledRecipe = RecipeCompiler.compileRecipe(recipe),
            implementations = mockImplementations)
        } should have('message ("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction"))
      }

      "a recipe does not provide an implementation for an interaction" in {
        val recipe = Recipe("MissingImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        intercept[BakerException] {
          new Baker(
            compiledRecipe = RecipeCompiler.compileRecipe(recipe),
            implementations = Map.empty[String, () => AnyRef])

        } should have('message ("No implementation provided for interaction: InteractionOne"))
      }

      "a recipe provides an implementation for an interaction and does not comply to the Interaction" in {
        val recipe = Recipe("WrongImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        intercept[BakerException] {
          new Baker(
            compiledRecipe = RecipeCompiler.compileRecipe(recipe),
            implementations = Map("InteractionOne" -> (() => new InteractionOneWrongApply())))

        } should have('message ("Invalid implementation provided for interaction: InteractionOne"))
      }
    }
  }
}
