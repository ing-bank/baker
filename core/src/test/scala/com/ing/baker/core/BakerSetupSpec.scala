package com.ing.baker.core

import com.ing.baker._
import com.ing.baker.compiler.RecipeValidationException
import com.ing.baker.scala_api._

import scala.concurrent.duration._
import scala.language.postfixOps

class BakerSetupSpec extends TestRecipeHelper {


  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  "The Baker execution engine during setup" should {

    "throw an RecipeValidationException if a recipe does not provide an implementation for an interaction" in {
      val recipe = Recipe(name = "MissingImplementation",
                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
                          events = Set.empty)

      a[RecipeValidationException] should be thrownBy {
        new Baker(recipe = recipe, implementations = Map.empty, actorSystem = defaultActorSystem)
      }
    }

    "throw an RecipeValidationException if an invalid recipe is given" in {
      val recipe = Recipe(name = "NonProvidedIngredient",
                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
                          events = Set.empty)

      a[RecipeValidationException] should be thrownBy {
        new Baker(recipe = recipe,
                  implementations = mockImplementations,
                  actorSystem = defaultActorSystem)
      }
    }

    "throw BakerException with the list of ingredient serialization validation errors" in {

      val recipe = Recipe(
        name = "NonSerializableIngredientTest",
        interactions = Seq(
          InteractionDescriptorFactory[NonSerializableIngredientInteraction]
        ),
        events = Set(classOf[InitialEvent])
      )

      intercept[NonSerializableException] {
        new Baker(recipe = recipe,
          implementations = mockImplementations,
          actorSystem = defaultActorSystem)
      } should have('message("Ingredient class: class com.ing.baker.NonSerializableObject is not serializable by akka"))

    }

  }
}
