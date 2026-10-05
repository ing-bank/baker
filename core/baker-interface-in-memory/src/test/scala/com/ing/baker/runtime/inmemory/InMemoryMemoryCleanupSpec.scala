package com.ing.baker.runtime.inmemory

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.recipe.TestRecipe.{InteractionOneSuccessful, initialEvent, interactionOne}
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.catseffect.EffectSupport
import com.ing.baker.runtime.model.{BakerConfig, BakerF, InteractionInstance}
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.{Outcome, Retries, Tag}

import java.util.UUID
import java.util.concurrent.CompletableFuture
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.jdk.DurationConverters._
import scala.reflect.ClassTag

object Retryable extends Tag("Retryable")

class InMemoryMemoryCleanupSpec extends AnyFlatSpec with Matchers with Retries {

  // Implicit ExecutionContext for Future operations
  implicit val executionContext: scala.concurrent.ExecutionContext = scala.concurrent.ExecutionContext.global

  // Implicit EffectSupport for Future
  implicit val effectSupportForFuture: EffectSupport[Future] =
    new EffectSupport[Future] {
      override def pure[A](value: A): Future[A] = Future.successful(value)
      override def map[A, B](fa: Future[A])(f: A => B): Future[B] = fa.map(f)
    }

  implicit val classTagFuture: ClassTag[Future[Any]] = ClassTag(classOf[Future[Any]])

  private def assertThrowsCause[T <: Throwable](f: => Unit)(implicit manifest: scala.reflect.Manifest[T]): Unit = {
    try {
      f
      fail(s"Expected ${manifest.runtimeClass.getSimpleName} but no exception was thrown")
    } catch {
      case e: java.util.concurrent.CompletionException =>
        val cause = e.getCause
        if (!manifest.runtimeClass.isInstance(cause)) {
          fail(s"Expected ${manifest.runtimeClass.getSimpleName} but got ${cause.getClass.getSimpleName}: ${cause.getMessage}")
        }
      case e: Throwable =>
        if (!manifest.runtimeClass.isInstance(e)) {
          fail(s"Expected ${manifest.runtimeClass.getSimpleName} but got ${e.getClass.getSimpleName}: ${e.getMessage}")
        }
    }
  }

  override def withFixture(test: NoArgTest): Outcome = {
    if (isRetryable(test))
      withRetry {
        super.withFixture(test)
      }
    else
      super.withFixture(test)
  }

  private def buildBaker(config: BakerConfig, interactions: List[InteractionInstance[Future]]): CompletableFuture[BakerF[CompletableFuture]] =
    InMemoryBaker.build(config, interactions).asInstanceOf[CompletableFuture[BakerF[CompletableFuture]]]

  behavior of "InMemoryRecipeInstanceManager"

  it should "find a process in the timeout" in {
    val recipeInstanceId = UUID.randomUUID().toString

    val baker = buildBaker(
      BakerConfig.default()
      .withIdleTimeout(100.milliseconds.toJava)
      .withAllowAddingRecipeWithoutRequiringInstances(true), List.empty)
      .join()

    val recipe = RecipeCompiler.compileRecipe(TestRecipe.getRecipe("InMemory"))

    val recipeId: String = recipe.recipeId
    baker.addRecipe(recipe, validate = false).join()
    baker.bake(recipeId, recipeInstanceId).join()
    baker.getRecipeInstanceState(recipeInstanceId).join()
  }

  it should "delete a process after the RetentionPeriod if RetentionPeriod is defined" in {
    val recipe = Recipe("tempRecipe1")
      .withInteractions(
        interactionOne
      )
      .withSensoryEvents(initialEvent)
      .withRetentionPeriod(100.milliseconds)

    class InteractionOneInterfaceImplementation extends TestRecipe.InteractionOne {
      override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
        Future.successful(InteractionOneSuccessful("output"))
      }
    }

    val recipeInstanceId = UUID.randomUUID().toString

    val baker = buildBaker(
      BakerConfig.default()
        .withIdleTimeout(10.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
      List(InteractionInstance.unsafeFrom[Future](new InteractionOneInterfaceImplementation())))
      .join()

    val recipeId: String = RecipeCompiler.compileRecipe(recipe).recipeId
    baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false).join()
    baker.bake(recipeId, recipeInstanceId).join()
    Thread.sleep(120)

    assertThrowsCause[NoSuchProcessException](baker.getRecipeInstanceState(recipeInstanceId).join())
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

    val baker = buildBaker(
      BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
      List(InteractionInstance.unsafeFrom[Future](new InteractionOneInterfaceImplementation())))
      .join()

    val recipeId: String = RecipeCompiler.compileRecipe(recipe).recipeId
    baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false).join()
    baker.bake(recipeId, recipeInstanceId).join()
    Thread.sleep(200)

    assertThrowsCause[NoSuchProcessException](baker.getRecipeInstanceState(recipeInstanceId).join())
  }

  it should "not delete a process after the Idle Timeout if it is still executing" in {
    val recipe = Recipe("tempRecipe3")
      .withInteractions(
        interactionOne
          .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
            initialDelay = 5.milliseconds, maximumRetries = 100, maxTimeBetweenRetries = Some(5.milliseconds))),
      )
      .withSensoryEvents(initialEvent)

    class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
      override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
        Future.failed(new RuntimeException("Failing interaction"))
      }
    }

    val recipeInstanceId = UUID.randomUUID().toString

    val baker = buildBaker(
      BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
      List(InteractionInstance.unsafeFrom[Future](new InteractionOneInterfaceImplementation())))
      .join()

    val recipeId: String = RecipeCompiler.compileRecipe(recipe).recipeId
    baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false).join()
    baker.bake(recipeId, recipeInstanceId).join()
    Thread.sleep(120)

    val result: RecipeInstanceState = baker.getRecipeInstanceState(recipeInstanceId).join()
    result should not be null
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

    val baker = buildBaker(
      BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
      List(InteractionInstance.unsafeFrom[Future](new InteractionOneInterfaceImplementation())))
      .join()

    val recipeId: String = RecipeCompiler.compileRecipe(recipe).recipeId
    baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false).join()
    baker.bake(recipeId, recipeInstanceId).join()
    Thread.sleep(80)
    Thread.sleep(80)

    val result: RecipeInstanceState = baker.getRecipeInstanceState(recipeInstanceId).join()
    result should not be null
  }

  it should "delete a process after the RetentionPeriod if it is still executing" in {
    val recipe = Recipe("tempRecipe4")
      .withInteractions(
        interactionOne
          .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(
            initialDelay = 5.milliseconds, maximumRetries = 100, maxTimeBetweenRetries = Some(5.milliseconds))),
      )
      .withSensoryEvents(initialEvent)
      .withRetentionPeriod(100.milliseconds)

    class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
      override def apply(recipeInstanceId: String, initialIngredient: String): Future[InteractionOneSuccessful] = {
        Future.failed(new RuntimeException("Failing interaction"))
      }
    }

    val recipeInstanceId = UUID.randomUUID().toString

    val baker = buildBaker(
      BakerConfig.default()
        .withIdleTimeout(100.milliseconds.toJava)
        .withRetentionPeriodCheckInterval(10.milliseconds.toJava)
        .withAllowAddingRecipeWithoutRequiringInstances(true),
      List(InteractionInstance.unsafeFrom[Future](new InteractionOneInterfaceImplementation())))
      .join()

    val recipeId: String = RecipeCompiler.compileRecipe(recipe).recipeId
    baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false).join()
    baker.bake(recipeId, recipeInstanceId).join()
    Thread.sleep(120)

    assertThrowsCause[NoSuchProcessException](baker.getRecipeInstanceState(recipeInstanceId).join())
  }
}
