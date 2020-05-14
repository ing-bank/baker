package com.ing.baker.test.scaladsl

import java.util.UUID

import akka.actor.ActorSystem
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.test.recipe.WebshopBaker._
import com.ing.baker.test.recipe.WebshopRecipe
import com.ing.baker.test.recipe.WebshopRecipe.{ItemsReserved, OrderPlaced}
import com.typesafe.config.ConfigFactory
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec
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

    BakerAssert.apply(baker, recipeInstanceId)
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
    val bakerAssert = createBakerAssert()
    Try(bakerAssert
      .waitFor(WebshopRecipe.happyFlow)
      .logEvents()
      .assertEventsFlow(WebshopRecipe.happyFlow -- classOf[ItemsReserved])) match {
      case Failure(exception: AssertionError) => log.info(exception.getMessage)
      case default => fail(s"assertion error is expected but got $default")
    }
  }
}
