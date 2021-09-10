package com.ing.baker.test.common

import java.util

import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.test.scaladsl.BakerEventsFlow
import com.ing.baker.test.{javadsl, scaladsl}
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.{Duration, _}
import scala.concurrent.{Await, Awaitable}
import scala.util.{Failure, Success, Try}


object BakerAssert {
  val DEFAULT_TIMEOUT: Duration = 10 seconds
}

trait BakerAssert[Flow] extends LazyLogging {

  // to implement

  protected def baker: Baker

  protected def recipeInstanceId: String

  protected def timeout: Duration = BakerAssert.DEFAULT_TIMEOUT

  // initialization

  private val bakerAsync = new BakerAsync(baker)

  // async

  def waitFor(flow: Flow): BakerAssert[Flow] = {
    val expectedFlow = toScalaEventsFlow(flow)
    Try(bakerAsync.waitFor(recipeInstanceId, expectedFlow)) match {
      case Success(_) => // nothing
      case Failure(_) => {
        val actualFlow = this.getActualFlow
        val dif1 = expectedFlow --- actualFlow
        val dif2 = actualFlow --- expectedFlow
        throw new AssertionError(s"""
             |${Console.RED   }Timeout waiting for the events flow:
             |${Console.YELLOW}    actual: $actualFlow
             |${Console.GREEN }  expected: $expectedFlow
             |${Console.RED   }difference: ${if(dif1.events.nonEmpty) s"++ $dif1"}
             |${Console.RED   }            ${if(dif2.events.nonEmpty) s"-- $dif2"}
             |""".stripMargin)
      }
    }
    this
  }

  // assertion

  def assertEventsFlow(flow: Flow): BakerAssert[Flow] = {
    val expectedFlow = toScalaEventsFlow(flow)
    val actualFlow = this.getActualFlow
    logInfoOnError(assert(expectedFlow == actualFlow,
      s"""
         |Events are not equal:
         |     actual: ${actualFlow}
         |   expected: ${expectedFlow}
         | difference: ${(expectedFlow --- actualFlow) ::: (actualFlow --- expectedFlow)}
         |""".stripMargin))
    this
  }

  def assertIngredient(name: String): IngredientAssert[Flow] = {
    val value: Value = await(baker.getIngredients(recipeInstanceId))(name)
    new IngredientAssert[Flow](this, value, assertion => logInfoOnError(assertion))
  }

  // logging

  def logIngredients(): BakerAssert[Flow] = {
    await(baker.getIngredients(recipeInstanceId).andThen {
      case Success(ingredients) => logger.info(s"Ingredients: $ingredients")
    })
    this
  }

  def logEventNames(): BakerAssert[Flow] = {
    await(baker.getEventNames(recipeInstanceId).andThen {
      case Success(names) => logger.info(s"Event Names: $names")
    })
    this
  }

  def logVisualState(): BakerAssert[Flow] = {
    await(baker.getVisualState(recipeInstanceId).andThen {
      case Success(visualState) => logger.info(s"VisualState: $visualState")
    })
    this
  }


  // private helper functions

  private def getActualFlow = await(baker.getEvents(recipeInstanceId)
    .map(events => BakerEventsFlow.apply(events.map(_.name).toSet)))

  private def toScalaEventsFlow(flow: Flow): scaladsl.BakerEventsFlow =
    flow match {
      case sf: scaladsl.BakerEventsFlow => sf
      case jf: javadsl.BakerEventsFlow =>
        val events: util.Set[String] = jf.getEvents
        val array = events.toArray(Array.empty[String])
        scaladsl.BakerEventsFlow(array:_*)
      case _ => throw new AssertionError(s"Unknown flow implementation: $flow")
    }

  private def await[T](fn: Awaitable[T]): T = Await.result(fn, timeout)

  private def logInfoOnError[T](assert: => T): T = Try(assert) match {
    case Success(v) => v // do nothing
    case Failure(f) =>
      logEventNames()
      logIngredients()
      logVisualState()
      throw f
  }
}
