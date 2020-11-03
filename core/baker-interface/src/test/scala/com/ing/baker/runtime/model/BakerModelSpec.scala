package com.ing.baker.runtime.model

import java.util.UUID

import cats.implicits._
import cats.effect.{ConcurrentEffect, IO, Resource, Sync}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceF}
import com.ing.bakery.utils.BakeryFunSpec
import org.mockito.Matchers.anyString
import org.mockito.Mockito.{verify, when}
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.mockito.MockitoSugar

import scala.reflect.ClassTag

abstract class BakerModelSpec[F[_]]
  extends BakeryFunSpec[F]
    with BakerModelFixtures[F]
    with Matchers
    with MockitoSugar {

  def runTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {

    test("execute an interaction when its ingredient is provided") { context =>
      val recipe =
        Recipe("IngredientProvidedRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        bakerWithRecipe <- context.setupBakerWithRecipe(recipe, mockImplementations)
        (baker, recipeId) = bakerWithRecipe
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield
        state.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue,
            "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }
  }

  case class Context(buildBaker: F[Baker[F]]) {

    def setupBakerWithRecipe(recipeName: String, appendUUIDToTheRecipeName: Boolean = true)(implicit effect: Sync[F], classTag: ClassTag[F[Any]]): F[(Baker[F], String)] = {
      val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
      val recipe = getRecipe(newRecipeName)
      for {
        _ <- setupMockResponse
        bakerAndRecipeId <- setupBakerWithRecipe(recipe, mockImplementations)
      } yield bakerAndRecipeId
    }

    def setupBakerWithRecipe(recipe: Recipe, implementations: Seq[InteractionInstanceF[F]])(implicit effect: Sync[F]): F[(Baker[F], String)] = {
      for {
        baker <- buildBaker
        _ <- baker.addInteractionInstances(implementations)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield (baker, recipeId)
    }

    def setupBakerWithNoRecipe(implicit effect: Sync[F], classTag: ClassTag[F[Any]]): F[Baker[F]] = {
      for {
        _ <- setupMockResponse
        baker <- buildBaker
        _ <- baker.addInteractionInstances(mockImplementations)
      } yield baker
    }

  }

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = Unit

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext]

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
