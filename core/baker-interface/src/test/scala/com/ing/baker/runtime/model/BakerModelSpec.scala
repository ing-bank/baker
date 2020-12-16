package com.ing.baker.runtime.model

import cats.effect.{ConcurrentEffect, IO, Resource, Sync}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.scaladsl.InteractionInstanceF
import com.ing.bakery.utils.BakeryFunSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfter, ConfigMap}

import java.util.UUID
import scala.reflect.ClassTag

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

  case class Context(buildBaker: List[InteractionInstanceF[F]] => F[BakerF[F]]) {

    def setupBakerWithRecipe(recipeName: String, implementations: List[InteractionInstanceF[F]] = List.empty, appendUUIDToTheRecipeName: Boolean = true)(implicit effect: Sync[F], classTag: ClassTag[F[Any]]): F[(BakerF[F], String)] = {
      val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
      val recipe = getRecipe(newRecipeName)
      for {
        _ <- setupMockResponse
        bakerAndRecipeId <- setupBakerWithRecipe(recipe, mockImplementations ++ implementations)
      } yield bakerAndRecipeId
    }

    def setupBakerWithRecipe(recipe: Recipe, implementations: List[InteractionInstanceF[F]])(implicit effect: Sync[F]): F[(BakerF[F], String)] = {
      for {
        baker <- buildBaker(implementations)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
      } yield (baker, recipeId)
    }

    def setupBakerWithNoRecipe(implementations: List[InteractionInstanceF[F]])(implicit effect: Sync[F], classTag: ClassTag[F[Any]]): F[BakerF[F]] = {
      for {
        _ <- setupMockResponse
        baker <- buildBaker(implementations ++ mockImplementations)
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
