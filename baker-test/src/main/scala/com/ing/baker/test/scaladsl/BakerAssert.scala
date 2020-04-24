package com.ing.baker.test.scaladsl

import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.language.postfixOps

final class BakerAssert(baker: Baker, recipeInstanceId: String) {

  private val bakerAsync = new BakerAsync(baker)

  // =======
  // asserts
  // =======

  def assertEventsFlow(expectedFlow: BakerEventsFlow, wait:Boolean = false): BakerAssert = {
    if (wait) {
      bakerAsync.waitFor(recipeInstanceId, expectedFlow)
    }

    val actualFlowFuture = for {
      actualEvents <- baker.getEvents(recipeInstanceId)
    } yield {
      BakerEventsFlow.apply(actualEvents.map(_.name).toSet)
    }

    val actualFlow = Await.result(actualFlowFuture, 10 seconds)
    assert(expectedFlow == actualFlow,
      s"""
         |Events are not equal:
         |   act: ${actualFlow}
         |   exp: ${expectedFlow}
         |  diff: ${(expectedFlow --- actualFlow) ::: (actualFlow --- expectedFlow)}
         |""".stripMargin)
    this
  }

  // ingredients

}

object BakerAssert {
  def apply(baker: Baker, recipeInstanceId: String): BakerAssert =
    new BakerAssert(baker, recipeInstanceId)
}
