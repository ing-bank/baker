package com.ing.baker.test.scaladsl

import com.ing.baker.runtime.scaladsl.Baker
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Awaitable}
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

class BakerAssert(_baker: Baker, _recipeInstanceId: String, timeout: Duration = 10 seconds) {
  private val log = LoggerFactory.getLogger(getClass)

  def baker: Baker = _baker

  def recipeInstanceId: String = _recipeInstanceId

  private val bakerAsync = new BakerAsync(baker)

  private[scaladsl] def await[T](fn: Awaitable[T]): T = Await.result(fn, timeout)

  private[scaladsl] def logInfoOnError[T](assert: => T): T = Try(assert) match {
    case Success(v) => v // do nothing
    case Failure(f) =>
      logEventNames()
      logIngredients()
      logVisualState()
      throw f
  }

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
    logInfoOnError(assert(expectedFlow == actualFlow,
      s"""
         |Events are not equal:
         |     actual: ${actualFlow}
         |   expected: ${expectedFlow}
         | difference: ${(expectedFlow --- actualFlow) ::: (actualFlow --- expectedFlow)}
         |""".stripMargin))
    this
  }

  // ===========
  // ingredients
  // ===========

  def assetIngredient(name: String): IngredientAssert = new IngredientAssert(this, name)

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
