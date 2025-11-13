package com.ing.baker.test

import cats.effect.IO
import cats.effect.unsafe.IORuntime
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.test.recipe.WebshopBaker.{baker, recipeId}
import com.ing.baker.test.recipe.WebshopRecipe.OrderPlaced
import com.ing.baker.test.recipe.{WebshopBaker, WebshopRecipe}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.time.SpanSugar.convertIntToGrainOfTime

import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration.Duration

class BakerAsyncTest extends AnyFlatSpec with Matchers {

  implicit val runtime: IORuntime = IORuntime.global

  "BakerAsync object" should "be created" in {
    new BakerAsync(WebshopBaker.baker)
  }

  it should "be successful for late event" in {
    cook(UUID.randomUUID().toString, 200.millis).unsafeRunSync()
  }

  it should "be successful for early event" in {
    cook(UUID.randomUUID().toString, 0.millis).unsafeRunSync()
  }

  it should "be successful for multiple events event" in {
    val test1 = cook(UUID.randomUUID().toString, 200.millis)
    val test2 = cook(UUID.randomUUID().toString, 200.millis)

    // Run both tests in parallel and wait for them to complete
    (test1, test2).parTupled.unsafeRunSync()
  }

  private def cook(recipeInstanceId: String, delay: Duration): IO[Unit] = {
    val sensoryEvent = EventInstance.unsafeFrom(OrderPlaced("order-1", "item-1" :: Nil))

    // Helper to convert a Future-based function into an IO
    def futureToIO[A](f: => Future[A]): IO[A] = IO.fromFuture(IO(f))

    val fireEventAction = futureToIO {
      baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, sensoryEvent)
    }

    for {
      _ <- futureToIO(baker.bake(recipeId, recipeInstanceId))

      _ <- if (delay.toMillis > 0) IO.sleep(delay) *> fireEventAction else fireEventAction

      _ <- futureToIO(new BakerAsync(baker).waitFor(recipeInstanceId, WebshopRecipe.happyFlow.events))
    } yield ()
  }
}