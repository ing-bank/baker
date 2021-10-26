package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.ScalaDSLRuntime._
import com.ing.baker.runtime.akka.implementations.{InteractionOneFieldName, InteractionOneInterfaceImplementation, InteractionOneWrongApply}
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, RecipeValidationException}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory
import org.mockito.Matchers.anyString
import org.mockito.Mockito.when

import scala.concurrent.Future
import scala.language.postfixOps


class BakerSetupSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "BakerSetupSpec"

  before {
    resetMocks()
  }

  "The Baker execution engine during setup" should {

    "bootstrap correctly without throwing an error if provided a correct recipe and correct implementations" when {

      "correctly load extensions when specified in the configuration" in {
        val simpleRecipe = RecipeCompiler.compileRecipe(Recipe("SimpleRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent))

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(mockImplementations))
        when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful("foobar")))
        for {
          recipeId <- baker.addRecipe(RecipeRecord.of(simpleRecipe))
          recipeInstanceId = java.util.UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, initialEvent.instance("initialIngredient"))
        } yield succeed
      }

      "providing implementations in a sequence" in {
        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(mockImplementations))
        for {
         _ <- baker.getAllRecipes
        } yield succeed
      }

      "providing an implementation with the class simplename same as the interaction" in {
        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(InteractionInstance.unsafeFrom(new implementations.InteractionOne())))
        for {
          _ <- baker.getAllRecipes
        } yield succeed
      }

      "providing an implementation for a renamed interaction" in {

        val recipe = Recipe("simpleNameImplementationWithRename")
          .withInteraction(interactionOne.withName("interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(InteractionInstance.unsafeFrom(new implementations.InteractionOne())))

        for {
          _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        } yield succeed
      }

      "providing an implementation with a name field" in {

        val recipe = Recipe("fieldNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(InteractionInstance.unsafeFrom(new InteractionOneFieldName())))

        for {
          _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        } yield succeed
      }

      "providing the implementation in a sequence with the interface its implementing with the correct name" in {

        val recipe = Recipe("interfaceImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))

        for {
          _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        } yield succeed
      }

      "the recipe contains complex ingredients that are serializable" in {
        val recipe = Recipe("complexIngredientInteractionRecipe")
          .withInteraction(interactionWithAComplexIngredient)
          .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(InteractionInstance.unsafeFrom(mock[ComplexIngredientInteraction])))

        for {
          _ <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        } yield succeed
      }
    }

    "throw a exception" when {
      "an invalid recipe is given" in {

        val recipe = Recipe("NonProvidedIngredient")
          .withInteraction(interactionOne)
          .withSensoryEvent(secondEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(mockImplementations))

        recoverToExceptionIf[RecipeValidationException] {
          baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        }.map(_ should have('message("Recipe NonProvidedIngredient:68b775e508fc6877 has validation errors: Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction")))
      }

      "a recipe does not provide an implementation for an interaction" in {

        val recipe = Recipe("MissingImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager())

        recoverToExceptionIf[ImplementationsException] {
          baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        }.map(_ should have('message("Recipe MissingImplementation:dc3970efc8837e64 has implementation errors: No compatible implementation provided for interaction: InteractionOne: List(NameNotFound)")))
      }

      "a recipe provides an implementation for an interaction and does not comply to the Interaction" in {

        val recipe = Recipe("WrongImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem, CachingInteractionManager(InteractionInstance.unsafeFrom(new InteractionOneWrongApply())))

        recoverToExceptionIf[ImplementationsException] {
          baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        }.map(_ should have('message("Recipe WrongImplementation:8e2745de0bb0bde5 has implementation errors: No compatible implementation provided for interaction: InteractionOne: List(InteractionOne input size differs: transition expects 2, implementation provides 1)")))
      }
    }
  }
}
