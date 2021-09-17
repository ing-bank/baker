package com.ing.baker.test.scaladsl

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
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.util.{Failure, Try}

class RecipeAssertTest extends AnyFlatSpec with Matchers with StrictLogging {

  private def createBakerAssert(async: Boolean = false): RecipeAssert = {
    val recipeInstanceId = UUID.randomUUID().toString
    val sensoryEvent = EventInstance.unsafeFrom(OrderPlaced("order-1", "item-1" :: Nil))

    baker.bake(recipeId, recipeInstanceId)
    if (async) {
      Future {
        Thread.sleep(500)
        baker.fireEvent(recipeInstanceId, sensoryEvent)
      }
    } else {
      baker.fireEvent(recipeInstanceId, sensoryEvent)
    }

    RecipeAssert(baker, recipeInstanceId)
  }

  private def assertFail[T](assertion: => T): Unit = Try(assertion) match {
    case Failure(t: Throwable) => logger.info(t.getMessage)
    case default => fail(s"assertion error is expected but got $default")
  }

  "RecipeAssert object" should "be created" in {
    RecipeAssert.apply(baker, "someProcessId")
  }

  "assertEventsFlow" should "work with happy flow" in {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow)
  }

  "assertEventsFlow" should "work with some delay" in {
    createBakerAssert(true)
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow)
  }

  "assertEventsFlow" should "fail on incorrect events" in assertFail {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow -- classOf[ItemsReserved])
  }

  "assertIngredient" should "work for isEqual" in {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isEqual("order-1")
  }

  "assertIngredient" should "fail for isEqual" in assertFail {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isEqual("order-2")
  }

  "assertIngredient" should "work for isAbsent" in {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("non-existent").isAbsent
  }

  "assertIngredient" should "work for isNull" in assertFail {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isNull
  }

  "assertIngredient" should "work for customAssert" in {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").is(value => Assertions.assert(value.as[String] == "order-1"))
  }

  "assertIngredient" should "fail for customAssert" in assertFail {
    createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").is(value => Assertions.assert(value.as[String] == "order-2"))
  }
}
