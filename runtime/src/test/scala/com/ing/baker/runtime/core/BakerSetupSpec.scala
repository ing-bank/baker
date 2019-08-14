package com.ing.baker.runtime.core

import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.core.implementations.{InteractionOneFieldName, InteractionOneInterfaceImplementation, InteractionOneWrongApply}
import org.mockito.Matchers.anyString
import org.mockito.Mockito.when

import scala.language.postfixOps
import com.ing.baker.runtime.ScalaDSLRuntime._


class BakerSetupSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "BakerSetupSpec"

  before {
    resetMocks
  }

  "The Baker execution engine during setup" should {

    "bootstrap correctly without throwing an error if provided a correct recipe and correct implementations" when {


      "correcly load extensions when specified in the configuration" in {

        val simpleRecipe = RecipeCompiler.compileRecipe(Recipe("SimpleRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent))

        val baker = new Baker()

        baker.addImplementations(mockImplementations)

        when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(InteractionOneSuccessful("foobar"))

        val recipeId = baker.addRecipe(simpleRecipe)
        val processId = java.util.UUID.randomUUID().toString

        baker.bake(recipeId, processId)
        baker.processEvent(processId, initialEvent.instance("initialIngredient"))

      }

      "providing implementations in a sequence" in {

        val baker = new Baker()

        baker.addImplementations(mockImplementations)
      }

      "providing an implementation with the class simplename same as the interaction" in {

        val baker = new Baker()

        baker.addImplementation(new implementations.InteractionOne())
      }

      "providing an implementation for a renamed interaction" in {

        val recipe = Recipe("simpleNameImplementationWithRename")
          .withInteraction((interactionOne.withName("interactionOneRenamed")))
          .withSensoryEvent(initialEvent)

        val baker = new Baker()

        baker.addImplementation(new implementations.InteractionOne())

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }

      "providing an implementation with a name field" in {

        val recipe = Recipe("fieldNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker()

        baker.addImplementation(new InteractionOneFieldName())

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }

      "providing the implementation in a sequence with the interface its implementing with the correct name" in {

        val recipe = Recipe("interfaceImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker()

        baker.addImplementation(new InteractionOneInterfaceImplementation())

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }

      "the recipe contains complex ingredients that are serializable" in {
        val recipe = Recipe("complexIngredientInteractionRecipe")
          .withInteraction(complexIngredientInteraction)
          .withSensoryEvent(initialEvent)

        val baker = new Baker()

        baker.addImplementation(mock[ComplexIngredientInteraction])

        baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      }
    }

    "throw a exception" when {
      "an invalid recipe is given" in {

        val recipe = Recipe("NonProvidedIngredient")
          .withInteraction(interactionOne)
          .withSensoryEvent(secondEvent)

        val baker = new Baker()

        baker.addImplementations(mockImplementations)

        intercept[RecipeValidationException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } should have('message ("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction"))
      }

      "a recipe does not provide an implementation for an interaction" in {

        val recipe = Recipe("MissingImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker()

        intercept[BakerException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } should have('message ("No implementation provided for interaction: InteractionOne"))
      }

      // TODO uncheck ignore when fixed
      "a recipe provides an implementation for an interaction and does not comply to the Interaction" ignore {

        val recipe = Recipe("WrongImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = new Baker()

        baker.addImplementation(new InteractionOneWrongApply())

        intercept[BakerException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } should have('message ("No implementation provided for interaction: InteractionOne"))
      }
    }
  }
}
