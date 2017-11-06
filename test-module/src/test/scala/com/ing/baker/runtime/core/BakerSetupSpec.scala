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
          implementations = mockImplementations)
      }

      "providing the implementation in a sequence with the class simplename same as the interaction" in {
        val recipe = Recipe("simpleNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        new Baker(
          implementations = Seq(new implementations.InteractionOne()))
      }

      "providing the implementation in a sequence and interaction renamed" in {
        val recipe = Recipe("simpleNameImplementationWithRename")
          .withInteraction((interactionOne, "interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

        val baker = new Baker(implementations = Seq(new implementations.InteractionOne()))

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }

      "providing the implementation in a sequence with the field name same as the interaction" in {
        val recipe = Recipe("fieldNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker(implementations = Seq(new InteractionOneFieldName()))

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }

      "providing the implementation in a sequence with the interface its implementing with the correct name" in {
        val recipe = Recipe("interfaceImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker(implementations = Seq(new InteractionOneInterfaceImplementation()))

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }

      "the recipe contains complex ingredients that are serializable" in {
        val recipe = Recipe("complexIngredientInteractionRecipe")
          .withInteraction(complexIngredientInteraction)
          .withSensoryEvent(initialEvent)

        val baker = new Baker(implementations = Seq(mock[ComplexIngredientInteraction]))

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }
    }

    "throw a exception" when {
      "an invalid recipe is given" in {
        val recipe = Recipe("NonProvidedIngredient")
          .withInteraction(interactionOne)
          .withSensoryEvent(secondEvent)

        val baker = new Baker(implementations = mockImplementations)

        intercept[RecipeValidationException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } should have('message ("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction"))
      }

      "a recipe does not provide an implementation for an interaction" in {
        val recipe = Recipe("MissingImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker(implementations = Seq.empty)

        intercept[BakerException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } should have('message ("No implementation provided for interaction: InteractionOne"))
      }

      // TODO uncheck ignore when fixed
      "a recipe provides an implementation for an interaction and does not comply to the Interaction" ignore {
        val recipe = Recipe("WrongImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker(Seq(new InteractionOneWrongApply()))

        intercept[BakerException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } should have('message ("No implementation provided for interaction: InteractionOne"))
      }
    }
  }
}
