package com.ing.baker.test

import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.test.recipe.WebshopBaker.{baker, recipeId}
import com.ing.baker.test.recipe.WebshopRecipe.OrderPlaced
import com.ing.baker.test.recipe.{WebshopBaker, WebshopRecipe}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import java.util.UUID
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BakerAsyncTest extends AnyFlatSpec with Matchers {

  "BakerAsync object" should "be created" in {
    new BakerAsync(WebshopBaker.baker)
  }

  "BakerAsync object" should "be successful for late event" in {
    val future = cook(UUID.randomUUID().toString, 200 millis)
    Await.result(future, 1 second)
  }

  "BakerAsync object" should "be successful for early event" in {
    val future = cook(UUID.randomUUID().toString, 0 millis)
    Await.result(future, 1 second)
  }

  "BakerAsync object" should "be successful for multiple events event" in {
    val future1 = cook(UUID.randomUUID().toString, 200 millis)
    val future2 = cook(UUID.randomUUID().toString, 200 millis)
    Await.result(future1, 1 second)
    Await.result(future2, 100 millis)
  }

  private def cook(recipeInstanceId: String, delay: Duration): Future[Unit] = {
    val sensoryEvent = EventInstance.unsafeFrom(OrderPlaced("order-1", "item-1" :: Nil))
    baker.bake(recipeId, recipeInstanceId)

    if (delay.toMillis == 0) {
      baker.fireEvent(recipeInstanceId, sensoryEvent)
    } else {
      Future {
        Thread.sleep(delay.toMillis)
        baker.fireEvent(recipeInstanceId, sensoryEvent)
      }
    }

    new BakerAsync(WebshopBaker.baker)
      .waitFor(recipeInstanceId, WebshopRecipe.happyFlow.events)
  }
}