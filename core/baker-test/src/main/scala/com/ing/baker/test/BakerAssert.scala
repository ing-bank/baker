package com.ing.baker.test

import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.{javadsl, scaladsl}
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

import java.util.function.Consumer
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.{Duration, _}
import scala.concurrent.{Await, Future}
import scala.util.{Failure, Success, Try}

class BakerAssert(private val baker: Baker, recipeInstanceId: String, timeout: Duration) extends LazyLogging {
  self =>

  // initialization

  private val bakerAsync = new BakerAsync(baker)

  // async

  def waitFor(expected: EventsFlow): BakerAssert = Try(bakerAsync.waitFor(recipeInstanceId, expected.events, timeout)) match {
    case Success(_) => this
    case Failure(_) => await {
      this.getActualFlow.map(actual =>
        throw new AssertionError(errorMsg("Timeout waiting for the events flow", expected, actual)))
    }
  }

  // assertions

  def assertEventsFlow(expected: EventsFlow): BakerAssert = await {
    this.getActualFlow.map(actual =>
      assertWithLogging(assert(expected == actual, errorMsg("Events are not equal", expected, actual))))
  }

  def assertIngredient(name: String): IngredientAssert = Await.result({
    baker.getIngredients(recipeInstanceId).map { ingredients =>
      val value = if (ingredients.contains(name)) ingredients(name) else null
      new IngredientAssert(Option(value))
    }
  }, timeout)

  // logging

  def logIngredients(): BakerAssert = await {
    baker.getIngredients(recipeInstanceId).map(ingredients => logger.info(s"Ingredients: $ingredients"))
  }

  def logEventNames(): BakerAssert = await {
    baker.getEventNames(recipeInstanceId).map(names => logger.info(s"Event Names: $names"))
  }

  def logVisualState(): BakerAssert = await {
    baker.getVisualState(recipeInstanceId).map(visualState => logger.info(s"VisualState: $visualState"))
  }

  // private helper functions

  private def await(future: Future[_]): BakerAssert = {
    Try(Await.result(future, timeout)) match {
      case Success(_) =>
      case Failure(exception) => throw exception.getCause
    }
    this
  }

  private def getActualFlow: Future[EventsFlow] =
    baker.getEvents(recipeInstanceId).map(events => EventsFlow(events.map(_.name).toSet))

  private def assertWithLogging[T](assert: => T): BakerAssert = Try(assert) match {
    case Success(_) => this
    case Failure(throwable) =>
      logEventNames()
      logIngredients()
      logVisualState()
      throw throwable
  }

  private def errorMsg(msg: String, expected: EventsFlow, actual: EventsFlow): String = {
    val dif1 = expected --- actual
    val dif2 = actual --- expected
    s"""
       |${Console.RED}$msg:
       |${Console.YELLOW}    actual: $actual
       |${Console.GREEN}  expected: $expected
       |${Console.RED}difference: ${if (dif1.events.nonEmpty) s"++ $dif1"}
       |${Console.RED}            ${if (dif2.events.nonEmpty) s"-- $dif2"}
       |""".stripMargin
  }

  // ingredient assert

  class IngredientAssert(actual: Option[Value]) {

    def isNull: BakerAssert =
      is(value => assert(value.isNull, s"expect value '$value' to be null"))

    def isAbsent: BakerAssert =
      is(value => assert(value == null, s"expect value to be absent"))

    def isEqual(expected: Any): BakerAssert =
      is(value => assert(value.equalsObject(expected), s"expect value '$value' to be equal to '$expected'"))

    def is(assertion: Consumer[Value]): BakerAssert =
      assertWithLogging(assertion.accept(actual.orNull))
  }
}

object BakerAssert {
  val DEFAULT_TIMEOUT: Duration = 10 seconds

  def apply(baker: Baker, recipeInstanceId: String, timeout: Duration = DEFAULT_TIMEOUT) =
    new BakerAssert(baker, recipeInstanceId, timeout)

  def of(baker: javadsl.Baker, recipeInstanceId: String): BakerAssert =
    apply(baker, recipeInstanceId)

  def of(baker: javadsl.Baker, recipeInstanceId: String, timeout: java.time.Duration): BakerAssert =
    apply(baker, recipeInstanceId, timeout)

  private implicit def toScala(duration: java.time.Duration): Duration =
    Duration.fromNanos(duration.toNanos)

  // hack for now as there is no way to convert java baker to scala baker
  private implicit def toScala(baker: javadsl.Baker): scaladsl.Baker = {
    val field = classOf[javadsl.Baker].getDeclaredField("baker")
    try {
      field.setAccessible(true)
      field.get(baker).asInstanceOf[scaladsl.Baker]
    } finally {
      field.setAccessible(false)
    }
  }
}
