package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.akka.implementations.{InteractionOneFieldName, InteractionOneInterfaceImplementation, InteractionOneWrongApply}
import org.mockito.Matchers.anyString
import org.mockito.Mockito.when

import scala.language.postfixOps
import com.ing.baker.runtime.ScalaDSLRuntime._
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, RecipeValidationException}
import com.ing.baker.runtime.scaladsl.{Baker, InteractionInstance}
import com.typesafe.config.ConfigFactory

import scala.concurrent.Future


class BakerSetupSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "BakerSetupSpec"

  before {
    resetMocks()
  }

  "The Baker execution engine during setup" should {

    "bootstrap correctly without throwing an error if provided a correct recipe and correct implementations" when {

      "correcly load extensions when specified in the configuration" in {
        val simpleRecipe = RecipeCompiler.compileRecipe(Recipe("SimpleRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent))

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        for {
          _ <- baker.addImplementations(mockImplementations)
          _ = when (testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful("foobar")))
          recipeId <- baker.addRecipe(simpleRecipe)
          processId = java.util.UUID.randomUUID().toString
          _ <- baker.bake(recipeId, processId)
          _ <- baker.fireEventAndResolveWhenCompleted(processId, initialEvent.instance("initialIngredient"))
        } yield succeed
      }

      "providing implementations in a sequence" in {
        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)
        baker.addImplementations(mockImplementations).map(_ => succeed)
      }

      "providing an implementation with the class simplename same as the interaction" in {
        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)
        baker.addImplementation(InteractionInstance.unsafeFrom(new implementations.InteractionOne())).map(_ => succeed)
      }

      "providing an implementation for a renamed interaction" in {

        val recipe = Recipe("simpleNameImplementationWithRename")
          .withInteraction(interactionOne.withName("interactionOneRenamed"))
          .withSensoryEvent(initialEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        for {
          _ <- baker.addImplementation(InteractionInstance.unsafeFrom(new implementations.InteractionOne()))
          _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } yield succeed
      }

      "providing an implementation with a name field" in {

        val recipe = Recipe("fieldNameImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        for {
          _ <- baker.addImplementation(InteractionInstance.unsafeFrom(new InteractionOneFieldName()))
          _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } yield succeed
      }

      "providing the implementation in a sequence with the interface its implementing with the correct name" in {

        val recipe = Recipe("interfaceImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        for {
          _ <- baker.addImplementation(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation()))
          _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } yield succeed
      }

      "the recipe contains complex ingredients that are serializable" in {
        val recipe = Recipe("complexIngredientInteractionRecipe")
          .withInteraction(complexIngredientInteraction)
          .withSensoryEvent(initialEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        for {
          _ <- baker.addImplementation(InteractionInstance.unsafeFrom(mock[ComplexIngredientInteraction]))
          _ <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        } yield succeed
      }
    }

    "throw a exception" when {
      "an invalid recipe is given" in {

        val recipe = Recipe("NonProvidedIngredient")
          .withInteraction(interactionOne)
          .withSensoryEvent(secondEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        baker.addImplementations(mockImplementations)

        recoverToExceptionIf[RecipeValidationException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        }.map(_ should have('message ("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction")))
      }

      "a recipe does not provide an implementation for an interaction" in {

        val recipe = Recipe("MissingImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        recoverToExceptionIf[ImplementationsException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        }.map(_ should have('message ("No implementation provided for interaction: InteractionOne")))
      }

      "a recipe provides an implementation for an interaction and does not comply to the Interaction" in {

        val recipe = Recipe("WrongImplementation")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

        val baker = Baker.akka(ConfigFactory.load(), defaultActorSystem, defaultMaterializer)

        baker.addImplementation(InteractionInstance.unsafeFrom(new InteractionOneWrongApply()))

        recoverToExceptionIf[ImplementationsException] {
          baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
        }.map(_ should have('message ("No implementation provided for interaction: InteractionOne")))
      }
    }
  }
}
