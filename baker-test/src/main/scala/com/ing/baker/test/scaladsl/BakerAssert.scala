package com.ing.baker.test.scaladsl

import com.ing.baker.runtime.scaladsl.Baker
import org.slf4j.LoggerFactory

import scala.concurrent.{Await, Awaitable, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

final class BakerAssert(baker: Baker, recipeInstanceId: String) {
  private val log = LoggerFactory.getLogger(getClass)

  private val bakerAsync = new BakerAsync(baker)

  private val TIMEOUT = 10 seconds;

  private def await[T](fn: Awaitable[T]): T = Await.result(fn, TIMEOUT)

  // =====
  // async
  // =====

  def waitFor(flow: BakerEventsFlow): BakerAssert = {
    bakerAsync.waitFor(recipeInstanceId, flow)
    this
  }

  // =======
  // asserts
  // =======

  def assertEventsFlow(expectedFlow: BakerEventsFlow): BakerAssert = {
    val actualFlow = await(baker.getEvents(recipeInstanceId)
      .map(events => BakerEventsFlow.apply(events.map(_.name).toSet)))
    val t = Try(assert(expectedFlow == actualFlow,
      s"""
         |Events are not equal:
         |     actual: ${actualFlow}
         |   expected: ${expectedFlow}
         | difference: ${(expectedFlow --- actualFlow) ::: (actualFlow --- expectedFlow)}
         |""".stripMargin))
    t match {
      case Success(_) => // do nothing
      case Failure(f) =>
        logEventNames()
        logIngredients()
        logVisualState()
        throw f
    }
    this
  }

  // ===========
  // ingredients
  // ===========

  def assetIngredient(name: String): IngredientAssert = new IngredientAssert(this)

  // =======
  // logging
  // =======

  def logIngredients(): BakerAssert = {
    await(baker.getIngredients(recipeInstanceId).andThen {
      case Success(ingredients) => log.info(s"Ingredients: $ingredients")
    })
    this
  }

  def logEventNames(): BakerAssert = {
    await(baker.getEventNames(recipeInstanceId).andThen {
      case Success(names) => log.info(s"Event Names: $names")
    })
    this
  }

  def logVisualState(): BakerAssert = {
    await(baker.getVisualState(recipeInstanceId).andThen {
      case Success(visualState) => log.info(s"VisualState: $visualState")
    })
    this
  }
}

object BakerAssert {
  def apply(baker: Baker, recipeInstanceId: String): BakerAssert =
    new BakerAssert(baker, recipeInstanceId)
}
