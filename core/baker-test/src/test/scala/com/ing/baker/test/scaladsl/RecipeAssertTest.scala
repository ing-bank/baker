package com.ing.baker.test.scaladsl

import cats.effect.IO
import cats.effect.unsafe.IORuntime
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.test.RecipeAssert
import com.ing.baker.test.recipe.WebshopBaker._
import com.ing.baker.test.recipe.WebshopRecipe
import com.ing.baker.test.recipe.WebshopRecipe.{ItemsReserved, OrderPlaced}
import com.typesafe.scalalogging.StrictLogging
import org.scalatest.Assertions
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.util.{Failure, Try}

class RecipeAssertTest extends AnyFlatSpec with Matchers with StrictLogging {

  implicit val runtime: IORuntime = IORuntime.global

  private def createBakerAssert(async: Boolean = false): IO[RecipeAssert] = {
    val recipeInstanceId = UUID.randomUUID().toString
    val sensoryEvent = EventInstance.unsafeFrom(OrderPlaced("order-1", "item-1" :: Nil))

    // Helper to convert Baker's Future to IO
    def futureToIO[A](f: => Future[A]): IO[A] = IO.fromFuture(IO(f))

    val fireEventAction = futureToIO {
      baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, sensoryEvent)
    }

    for {
      _ <- futureToIO(baker.bake(recipeId, recipeInstanceId))
      _ <- if (async) IO.sleep(500.millis) *> fireEventAction else fireEventAction
    } yield {
      RecipeAssert(baker, recipeInstanceId)
    }
  }

  private def assertFail[T](assertion: => T): Unit = Try(assertion) match {
    case Failure(t: Throwable) => logger.info(s"Assertion failed as expected: ${t.getMessage}")
    case default => fail(s"assertion error is expected but got $default")
  }

  "RecipeAssert object" should "be created" in {
    RecipeAssert.apply(baker, "someProcessId")
  }

  "assertEventsFlow" should "work with happy flow" in {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow)
  }

  "assertEventsFlow" should "work with some delay" in {
    val recipeAssert = createBakerAssert(true).unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow)
  }

  "assertEventsFlow" should "fail on incorrect events" in assertFail {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow -- classOf[ItemsReserved])
  }

  "assertIngredient" should "work for isEqual" in {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isEqual("order-1")
  }

  "assertIngredient" should "fail for isEqual" in assertFail {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isEqual("order-2")
  }

  "assertIngredient" should "work for isAbsent" in {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("non-existent").isAbsent
  }

  "assertIngredient" should "fail for isNull" in assertFail {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isNull
  }

  "assertIngredient" should "work for customAssert" in {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").is(value => Assertions.assert(value.as[String] == "order-1"))
  }

  "assertIngredient" should "fail for customAssert" in assertFail {
    val recipeAssert = createBakerAssert().unsafeRunSync()
    recipeAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").is(value => Assertions.assert(value.as[String] == "order-2"))
  }
}