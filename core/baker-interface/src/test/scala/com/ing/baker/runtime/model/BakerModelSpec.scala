package com.ing.baker.runtime.model

import cats.effect.{Async, IO, Resource, Sync}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.bakery.utils.BakeryFunSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfter, ConfigMap}

import java.util.UUID
import scala.reflect.ClassTag

abstract class BakerModelSpec
  extends BakeryFunSpec
  with BakerModelSpecEnquireTests
  with BakerModelSpecSetupTests
  with BakerModelSpecExecutionSemanticsTests
  with BakerModelSpecEdgeCasesTests
  with BakerModelSpecFailureTests
  with BakerModelFixtures
  with Matchers
  with BeforeAndAfter {

  before {
    resetMocks()
  }

  def runAll()(implicit sync: Sync[IO], async: Async[IO], classTag: ClassTag[IO[Any]]): Unit = {
    runSetupTests()
    runEnquireTests()
    runExecutionSemanticsTests()
    runEdgeCasesTests()
    runFailureTests()
  }

  case class Context(buildBaker: List[InteractionInstance[IO]] => IO[BakerF[IO]]) {

    def setupBakerWithRecipe(recipeName: String, implementations: List[InteractionInstance[IO]] = List.empty, appendUUIDToTheRecipeName: Boolean = true)
                            (implicit sync: Sync[IO], classTag: ClassTag[IO[Any]]): IO[(BakerF[IO], String)] = {
      val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
      val recipe = getRecipe(newRecipeName)
      for {
        _ <- setupMockResponse
        bakerAndRecipeId <- setupBakerWithRecipe(recipe, mockImplementations ++ implementations)
      } yield bakerAndRecipeId
    }

    def setupBakerWithRecipe(recipe: Recipe, implementations: List[InteractionInstance[IO]])(implicit effect: Sync[IO]): IO[(BakerF[IO], String)] = {
      for {
        baker <- buildBaker(implementations)
        recipeId <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe), validate = true))
      } yield (baker, recipeId)
    }

    def setupBakerWithNoRecipe(implementations: List[InteractionInstance[IO]])(implicit sync: Sync[IO], classTag: ClassTag[IO[Any]]): IO[BakerF[IO]] = {
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
