package com.ing.baker.runtime.model

import java.util.concurrent.TimeUnit
import java.util.{Optional, UUID}

import cats.effect.{ConcurrentEffect, IO, Resource, Sync}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.InteractionFailureStrategy._
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, ProcessAlreadyExistsException, ProcessDeletedException}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceF, RecipeEventMetadata}
import com.ing.bakery.utils.BakeryFunSpec
import org.mockito.Matchers.{eq => mockitoEq, _}
import org.mockito.Mockito._
import org.scalatest.{BeforeAndAfter, ConfigMap}
import org.scalatest.matchers.should.Matchers
import com.ing.baker.runtime.model.ScalaDSLRuntime._
import com.ing.baker.types.{CharArray, Int32, PrimitiveValue}
import org.mockito.invocation.InvocationOnMock

import scala.reflect.ClassTag
import concurrent.duration._

abstract class BakerModelSpec[F[_]]
  extends BakeryFunSpec[F]
  with BakerModelSpecEnquireTests[F]
  with BakerModelSpecSetupTests[F]
  with BakerModelSpecExecutionSemanticsTests[F]
  with BakerModelSpecEdgeCasesTests[F]
  with BakerModelSpecFailureTests[F]
  with BakerModelFixtures[F]
  with Matchers
  with BeforeAndAfter {

  before {
    resetMocks()
  }

  def runAll()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {
    runSetupTests()
    runEnquireTests()
    runExecutionSemanticsTests()
    runEdgeCasesTests()
    runFailureTests()
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
