package com.ing.baker.runtime.core

import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.core.{NonSerializableException, RecipeValidationException}
import com.ing.baker.recipe.scaladsl.{InteractionDescriptorFactory, SRecipe}

import scala.concurrent.duration._
import scala.language.postfixOps

class BakerSetupSpec extends TestRecipeHelper {


  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  "The Baker execution engine during setup" should {

    "throw an RecipeValidationException if a recipe does not provide an implementation for an interaction" in {
      val recipe = SRecipe(name = "MissingImplementation",
                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
                          events = Set.empty)

      a[RecipeValidationException] should be thrownBy {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = Map.empty,
          actorSystem = defaultActorSystem)
      }
    }

    "throw an RecipeValidationException if an invalid recipe is given" in {
      val recipe = SRecipe(name = "NonProvidedIngredient",
                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
                          events = Set.empty)

      a[RecipeValidationException] should be thrownBy {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      }
    }

    "throw BakerException with the list of ingredient serialization validation errors for Ingredients provided by Interactions" in {

      val recipe = SRecipe(
        name = "NonSerializableIngredientTest",
        interactions = Seq(
          InteractionDescriptorFactory[NonSerializableIngredientInteraction]
        ),
        events = Set(classOf[InitialEvent])
      )

      intercept[NonSerializableException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      } should have('message("Ingredient nonSerializableIngredient of class com.ing.baker.NonSerializableObject is not serializable by akka"))

    }

    "throw BakerException with the list of ingredient serialization validation errors for Ingredients provided by Events" in {

      val recipe = SRecipe(
        name = "NonSerializableIngredientFromEventTest",
        interactions = Seq(),
        events = Set(classOf[EventWithANonSerializableIngredient])
      )

      intercept[NonSerializableException] {
        new Baker(
          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      } should have('message("Ingredient nonSerializableObject of class com.ing.baker.NonSerializableObject is not serializable by akka"))

    }

  }
}
