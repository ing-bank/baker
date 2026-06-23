package com.ing.baker.runtime.inmemory

import cats.effect.{Async, IO}
import cats.effect.unsafe.implicits.global
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.model.{BakerConfig, BakerF, InteractionInstance}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}
import org.scalatest.{Outcome, Retries}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.tagobjects.Retryable

import java.util.UUID
import scala.concurrent.duration._
import scala.concurrent.Future
import scala.jdk.DurationConverters._
import scala.reflect.ClassTag

class InMemoryMemoryCleanupSpec extends AnyFlatSpec with Matchers with Retries {

  // Implicit instances needed for InteractionInstance.unsafeFrom[IO]
  implicit val asyncIO: Async[IO] = IO.asyncForIO
  implicit val classTagIO: ClassTag[IO[Any]] = ClassTag(classOf[IO[_]])

  override def withFixture(test: NoArgTest): Outcome = {
    if (isRetryable(test))
      withRetry {
        super.withFixture(test)
      }
    else
      super.withFixture(test)
  }

  private def buildBaker(config: BakerConfig, interactions: List[InteractionInstance[IO]]): IO[BakerF[IO]] =
    InMemoryBaker.build(config, interactions).asInstanceOf[IO[BakerF[IO]]]

  behavior of "InMemoryRecipeInstanceManager"

  it should "find a process in the timeout" in {
    val recipeInstanceId = UUID.randomUUID().toString

    val result: IO[RecipeInstanceState] = for {
      baker <- buildBaker(BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true), List.empty)
      recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(TestRecipe.getRecipe("InMemory")), validate = false)
      _ <- baker.bake(recipeId, recipeInstanceId)
      result <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield result
    result.unsafeRunSync()
  }

  it should "delete a process after the RetentionPeriod if RetentionPeriod is defined" in {
    val recipe = Recipe("tempRecipe1")
      .withInteractions(
        interactionOne
      )
      .withSensoryEvents(initialEvent)
      .withRetentionPeriod(100 milliseconds)

    class InteractionOneInterfaceImplementation extends TestRecipe.InteractionOne {
      override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
        Future.successful(InteractionOneSuccessful("output"))
      }
    }

    val recipeInstanceId = UUID.randomUUID().toString

    val result: IO[RecipeInstanceState] = for {
      baker <- buildBaker(BakerConfig.default()
        .withIdleTimeout(10.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
        List(InteractionInstance.unsafeFrom[IO](new InteractionOneInterfaceImplementation())))
      recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
      _ <- baker.bake(recipeId, recipeInstanceId)
      _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAndForget()
      _ <- IO.sleep(120.milliseconds)
      result <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield result
    assertThrows[NoSuchProcessException](result.unsafeRunSync())
  }

  it should "delete a process after the idleTimeOut if the process is inactive" taggedAs Retryable in {
    val recipe = Recipe("tempRecipe2")
      .withInteractions(
        interactionOne
      )
      .withSensoryEvents(initialEvent)

    class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
      override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
        Future.successful(InteractionOneSuccessful("output"))
      }
    }

    val recipeInstanceId = UUID.randomUUID().toString

    val result: IO[RecipeInstanceState] = for {
      baker <- buildBaker(BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
        List(InteractionInstance.unsafeFrom[IO](new InteractionOneInterfaceImplementation())))
      recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
      _ <- baker.bake(recipeId, recipeInstanceId)
      _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAndForget()
      _ <- IO.sleep(200.milliseconds)
      result <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield result
    assertThrows[NoSuchProcessException](result.unsafeRunSync())
  }

  it should "not delete a process after the Idle Timeout if it is still executing" in {
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

    val recipeInstanceId = UUID.randomUUID().toString

    val result: IO[RecipeInstanceState] = for {
      baker <- buildBaker(BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
        List(InteractionInstance.unsafeFrom[IO](new InteractionOneInterfaceImplementation())))
      recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
      _ <- baker.bake(recipeId, recipeInstanceId)
      _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAndForget()
      _ <- IO.sleep(120.milliseconds)
      result <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield result
    result.unsafeRunSync()
  }

  it should "not delete a process if the idle timeout is reset due to activity" taggedAs Retryable in {
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

    val recipeInstanceId = UUID.randomUUID().toString

    val result: IO[RecipeInstanceState] = for {
      baker <- buildBaker(BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
        List(InteractionInstance.unsafeFrom[IO](new InteractionOneInterfaceImplementation())))
      recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
      _ <- baker.bake(recipeId, recipeInstanceId)
      _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAndForget()
      _ <- IO.sleep(80.milliseconds)
      _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAndForget()
      _ <- IO.sleep(80.milliseconds)
      result <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield result
    result.unsafeRunSync()
  }

  it should "delete a process after the RetentionPeriod if it is still executing" in {
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

    val recipeInstanceId = UUID.randomUUID().toString

    val result: IO[RecipeInstanceState] = for {
      baker <- buildBaker(BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
        List(InteractionInstance.unsafeFrom[IO](new InteractionOneInterfaceImplementation())))
      recipeId <- baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
      _ <- baker.bake(recipeId, recipeInstanceId)
      _ = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient"))).unsafeRunAndForget()
      _ <- IO.sleep(120.milliseconds)
      result <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield result
    assertThrows[NoSuchProcessException](result.unsafeRunSync())
  }
}
