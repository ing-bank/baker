package com.ing.baker.test.scaladsl

import java.util.UUID

import akka.actor.ActorSystem
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.test.recipe.WebshopBaker._
import com.ing.baker.test.recipe.WebshopRecipe
import com.ing.baker.test.recipe.WebshopRecipe.{ItemsReserved, OrderPlaced}
import com.typesafe.config.ConfigFactory
import org.scalatest.Assertions
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.util.{Failure, Try}

class BakerAssertTest extends AnyFlatSpec with Matchers {

  private val log = LoggerFactory.getLogger(getClass)

  private def createBakerAssert(async: Boolean = false): BakerAssert = {
    val recipeInstanceId = UUID.randomUUID().toString
    val sensoryEvent = EventInstance.unsafeFrom(OrderPlaced("order-1", "item-1" :: Nil))

    baker.bake(recipeId, recipeInstanceId)
    if (async) {
      Future {
        Thread.sleep(1000)
        baker.fireEvent(recipeInstanceId, sensoryEvent)
      }
    } else {
      baker.fireEvent(recipeInstanceId, sensoryEvent)
    }

    BakerAssert(baker, recipeInstanceId)
  }

  private def assertFail[T](assertion: => T): Unit =
    Try(assertion) match {
      case Failure(t: Throwable) => log.info(t.getMessage)
      case default => fail(s"assertion error is expected but got $default")
    }

  "BakerAssert object" should "be created" in {
    val baker = AkkaBaker(ConfigFactory.load, ActorSystem.apply("test"))
    BakerAssert.apply(baker, "someProcessId")
  }

  "assertEventsFlow" should "work with happy flow" in {
    val bakerAssert = createBakerAssert()
    bakerAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow)
  }

  "assertEventsFlow" should "work with some delay" in {
    val bakerAssert = createBakerAssert(true)
    bakerAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow)
  }

  "assertEventsFlow" should "fail on incorrect events" in {
    assertFail(createBakerAssert()
      .waitFor(WebshopRecipe.happyFlow)
      .assertEventsFlow(WebshopRecipe.happyFlow -- classOf[ItemsReserved]))
  }

  "assertIngredient" should "work for isEqual" in {
    val bakerAssert = createBakerAssert()
    bakerAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isEqual("order-1")
  }

  "assertIngredient" should "fail for isEqual" in {
    val bakerAssert = createBakerAssert()
    assertFail(bakerAssert.waitFor(WebshopRecipe.happyFlow)
    .assertIngredient("orderId").isEqual("order-2"))
  }

  "assertIngredient" should "work for notNull" in {
    val bakerAssert = createBakerAssert()
    bakerAssert
      .waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").notNull()
  }

  "assertIngredient" should "work for isNull" in {
    val bakerAssert = createBakerAssert()
    assertFail(bakerAssert.waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").isNull)
  }

  "assertIngredient" should "work for customAssert" in {
    val bakerAssert = createBakerAssert()
    bakerAssert.waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").is(value => Assertions.assert(value.as[String] == "order-1"))
  }

  "assertIngredient" should "fail for customAssert" in {
    val bakerAssert = createBakerAssert()
    assertFail(bakerAssert.waitFor(WebshopRecipe.happyFlow)
      .assertIngredient("orderId").is(value => Assertions.assert(value.as[String] == "order-2")))
  }
}
