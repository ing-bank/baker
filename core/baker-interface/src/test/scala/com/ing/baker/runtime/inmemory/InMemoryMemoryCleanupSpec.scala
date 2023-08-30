package com.ing.baker.runtime.inmemory

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.model.{BakerF, InteractionInstance}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers

import java.util.UUID
import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class InMemoryMemoryCleanupSpec extends AnyFunSpec with Matchers {
  describe("InMemoryRecipeInstanceManager") {
    it("should find a process in the timeout") {
      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(idleTimeout = 100.milliseconds, allowAddingRecipeWithoutRequiringInstances = true), List.empty)
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(TestRecipe.getRecipe("InMemory")), validate = false)
        _ <- baker.bake(recipeId, recipeInstanceId)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      result.unsafeRunSync()
    }

    it("should delete a process after the RetentionPeriod if RetentionPeriod is defined") {
      val recipe = Recipe("tempRecipe1")
        .withInteractions(
          interactionOne
        )
        .withSensoryEvents(initialEvent)
        .withRetentionPeriod(100 milliseconds)

      class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
        override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
          println("Interaction executing")
          Future.successful(new InteractionOneSuccessful("output"))
        }
      }

      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(
          idleTimeout = 10.milliseconds,
          retentionPeriodCheckInterval = 10.milliseconds,
          allowAddingRecipeWithoutRequiringInstances = true),
          List(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAsyncAndForget()
        _ <- IO.sleep(120.milliseconds)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      assertThrows[NoSuchProcessException](result.unsafeRunSync())
    }

    it("should delete a process after the idleTimeOut if the process is inactive") {
      val recipe = Recipe("tempRecipe2")
        .withInteractions(
          interactionOne
        )
        .withSensoryEvents(initialEvent)

      class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
        override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
          Future.successful(new InteractionOneSuccessful("output"))
        }
      }

      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(
          idleTimeout = 100.milliseconds,
          retentionPeriodCheckInterval = 10.milliseconds,
          allowAddingRecipeWithoutRequiringInstances = true),
          List(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAsyncAndForget()
        _ <- IO.sleep(200.milliseconds)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      assertThrows[NoSuchProcessException](result.unsafeRunSync())
    }

    it("should not delete a process after the Idle Timeout if it is still executing") {
      val recipe = Recipe("tempRecipe3")
        .withInteractions(
          interactionOne
            .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
              initialDelay = 5 millisecond, maximumRetries = 100, maxTimeBetweenRetries = Some(5 milliseconds))),
        )
        .withSensoryEvents(initialEvent)

      class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
        override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
          Future.failed(new RuntimeException("Failing interaction"))
        }
      }

      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(
          idleTimeout = 100.milliseconds,
          retentionPeriodCheckInterval = 10.milliseconds,
          allowAddingRecipeWithoutRequiringInstances = true),
          List(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAsyncAndForget()
        _ <- IO.sleep(120.milliseconds)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      result.unsafeRunSync()
    }

    it("should not delete a process if the idle timeout is reset due to activity") {
      val recipe = Recipe("tempRecipe3")
        .withInteractions(
          interactionOne
        )
        .withSensoryEvents(initialEvent)

      class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
        override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
          Future.failed(new RuntimeException("Failing interaction"))
        }
      }

      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(
          idleTimeout = 100.milliseconds,
          retentionPeriodCheckInterval = 10.milliseconds,
          allowAddingRecipeWithoutRequiringInstances = true),
          List(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAsyncAndForget()
        _ <- IO.sleep(80.milliseconds)
        _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAsyncAndForget()
        _ <- IO.sleep(80.milliseconds)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      result.unsafeRunSync()
    }

    it("should delete a process after the RetentionPeriod if it is still executing") {
      val recipe = Recipe("tempRecipe4")
        .withInteractions(
          interactionOne
            .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
              initialDelay = 5 millisecond, maximumRetries = 100, maxTimeBetweenRetries = Some(5 milliseconds))),
        )
        .withSensoryEvents(initialEvent)
        .withRetentionPeriod(100 milliseconds)

      class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
        override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
          Future.failed(new RuntimeException("Failing interaction"))
        }
      }

      implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
      implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

      val recipeInstanceId = UUID.randomUUID().toString

      val result: IO[RecipeInstanceState] = for {
        baker <- InMemoryBaker.build(BakerF.Config(
          idleTimeout = 100.milliseconds,
          retentionPeriodCheckInterval = 10.milliseconds,
          allowAddingRecipeWithoutRequiringInstances = true),
          List(InteractionInstance.unsafeFrom(new InteractionOneInterfaceImplementation())))
        recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAsyncAndForget()
        _ <- IO.sleep(120.milliseconds)
        result <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield (result)
      assertThrows[NoSuchProcessException](result.unsafeRunSync())
    }
  }
}
