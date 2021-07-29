package com.ing.baker.runtime.inmemory

import java.util.UUID

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.model.BakerF
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

class InMemoryMemoryCleanupSpec extends AnyFunSpec with Matchers {
  describe("InMemoryRecipeInstanceManager") {
    describe("should find a process in the timeout") {
      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(retentionPeriodCheckInterval = 100.milliseconds, allowAddingRecipeWithoutRequiringInstances = true), List.empty)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(TestRecipe.getRecipe("InMemory")))
        _ <- baker.bake(recipeId, recipeInstanceId)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      result.unsafeRunSync()
    }

    describe("should delete a process after the timeout") {
      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(retentionPeriodCheckInterval = 100.milliseconds, allowAddingRecipeWithoutRequiringInstances = true), List.empty)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(TestRecipe.getRecipe("InMemory")))
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.getRecipeInstanceState(recipeInstanceId)
        _ <- IO.sleep(110.milliseconds)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      assertThrows[NoSuchProcessException](result.unsafeRunSync())
    }
  }
}
