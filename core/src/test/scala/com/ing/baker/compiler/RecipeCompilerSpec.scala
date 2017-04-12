package com.ing.baker.compiler

import com.ing.baker._
import com.ing.baker.core.Baker
import com.ing.baker.scala_api._
import org.mockito.Matchers._
import org.mockito.Mockito._

import scala.concurrent.duration._
import scala.language.postfixOps

class RecipeCompilerSpec extends TestRecipeHelper {


  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  "The RecipeCompiler after compilation" should {

    "should not contain errors if compiling a valid recipe" in {
      val compiledRecipe: CompiledRecipe = getComplexRecipe("ValidRecipe").compileRecipe
      //For now all missing implementation errors are provided so they are filtered out
      compiledRecipe.validationErrors.filterNot(s => s.startsWith("No implementation provided for interaction")) shouldBe List.empty
    }

    "give a List of missing implementations in the validation errors if a recipe does not provide an implementation for an interaction" in {
      val recipe = SRecipe(name = "MissingImplementation",
                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
                          events = Set.empty)

      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain("No implementation provided for interaction: interface com.ing.baker.InteractionOne")
    }

    "give a List of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction" in {
      val recipe = SRecipe(name = "NonProvidedIngredient",
                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
                          events = Set.empty)

      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain ("Ingredient 'initialIngredient' for interaction 'interface com.ing.baker.InteractionOne:apply' is not provided by any event or interaction")
    }

    "give a list of non serializable events an RecipeValidationException if an event is not Serializable" in {

      val recipe = SRecipe(
        name = "NonSerializableEventTest",
        interactions = Seq(
          InteractionDescriptorFactory[NonSerializableEventInteraction]
        ),
        events = Set(classOf[InitialEvent])
      )
      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain ("Event class: class com.ing.baker.NonSerializableObject does not extend from com.ing.baker.api.Event")
    }

    "give a list of sensory events that does not extend from baker Event" in {

      val recipe = SRecipe(
        name = "NonSerializableSensoryEventTest",
        interactions = Seq(
          InteractionDescriptorFactory[InteractionOne]
        ),
        events = Set(classOf[InitialEvent], classOf[NonSerializableObject])
      )

      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain ("Event class: class com.ing.baker.NonSerializableObject does not extend from com.ing.baker.api.Event")
    }

    "give a list of wrong interactions if an event of an interaction does not match it's return type" in {
      val recipe = SRecipe(
        name = "NonMatchingReturnTypeTest",
        interactions = Seq(
          InteractionDescriptorFactory[NonMatchingReturnTypeInteraction]
        ),
        events = Set(classOf[InitialEvent])
      )
      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain ("Event class: class com.ing.baker.EventFromInteractionTwo is not assignable to return type: class java.lang.String for interaction: NonMatchingReturnTypeInteraction")
    }

    "give a list of wrong ingredients if an predefined ingredient is of the wrong type" in {
      val recipe = SRecipe(
        name = "WrongGivenIngredient",
        interactions = Seq(
          InteractionDescriptorFactory[InteractionOne]
                .withRequiredEvent[InitialEvent]
                .withPredefinedIngredients(("initialIngredient", null))
        ),
        events = Set(classOf[InitialEvent])
      )
      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain ("Predefined argument 'initialIngredient' is not of type: class java.lang.String on interaction: 'InteractionOne'")
    }

    "give a list of wrong ingredients if an predefined ingredient is not needed by the interaction" in {
      val recipe = SRecipe(
        name = "WrongGivenIngredient",
        interactions = Seq(
          InteractionDescriptorFactory[InteractionOne]
            .withPredefinedIngredients(("WrongIngredient", null))
        ),
        events = Set(classOf[InitialEvent])
      )
      val compiledRecipe: CompiledRecipe = recipe.compileRecipe
      compiledRecipe.validationErrors should contain ("Predefined argument 'WrongIngredient' is not defined on interaction: 'InteractionOne'")
    }
  }
}
