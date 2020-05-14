package com.ing.baker.test.scaladsl

import com.ing.baker.runtime.scaladsl.Baker
import org.slf4j.LoggerFactory

import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.language.postfixOps

final class BakerAssert(baker: Baker, recipeInstanceId: String) {
  private val log = LoggerFactory.getLogger(getClass)

  private val bakerAsync = new BakerAsync(baker)

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
    val actualFlowFuture = for {
      actualEvents <- baker.getEvents(recipeInstanceId)
    } yield BakerEventsFlow.apply(actualEvents.map(_.name).toSet)

    val actualFlow = Await.result(actualFlowFuture, 10 seconds)
    println(s"$actualFlow vs $expectedFlow")
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


  // logging

  def logEvents(): BakerAssert = {
    baker.getEvents(recipeInstanceId).andThen {
      case events => log.info(s"$events")
    }
    this
  }
}

object BakerAssert {
  def apply(baker: Baker, recipeInstanceId: String): BakerAssert =
    new BakerAssert(baker, recipeInstanceId)
}
