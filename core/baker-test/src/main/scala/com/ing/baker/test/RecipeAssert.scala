package com.ing.baker.test

import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.{javadsl, scaladsl}
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

import java.util.concurrent.ExecutionException
import java.util.function.Consumer
import scala.annotation.varargs
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.{Duration, _}
import scala.concurrent.{Await, Future}
import scala.util.{Failure, Success, Try}

class RecipeAssert(private val baker: Baker, private val recipeInstanceId: String, private val timeout: Duration) extends LazyLogging {

  // initialization

  private val bakerAsync = new BakerAsync(baker)

  // async

  def waitFor(expected: EventsFlow): RecipeAssert = await(bakerAsync.waitFor(recipeInstanceId, expected.events)) match {
    case Success(_) => this
    case Failure(_) => verify {
      this.getActualFlow.map(actual =>
        throw new AssertionError(errorMsg("Timeout waiting for the events flow", expected, actual)))
    }
  }

  // assertions

  def assertEventsFlow(expected: EventsFlow): RecipeAssert = verify {
    this.getActualFlow.map(actual => assert(expected == actual, errorMsg("Events are not equal", expected, actual)))
  }

  @varargs def assertEventNamesHappened(expectedEventNames: String*): RecipeAssert = verify{
    this.getActualFlow.map { actual =>
      val actualRelevantEvents = expectedEventNames.filter(expected => actual.events.contains(expected))
      assert(expectedEventNames.length == actualRelevantEvents.length,
        errorMsg("Not all expected events have happened", EventsFlow.of(expectedEventNames:_*), EventsFlow.of(actualRelevantEvents:_*)))
    }
  }

  @varargs def assertEventNamesNotHappened(forbiddenEventNames: String*): RecipeAssert = verify {
    this.getActualFlow.map { actual =>
      val actualUnexpectedEvents = forbiddenEventNames.filter(forbidden => actual.events.contains(forbidden))
      assert(actualUnexpectedEvents.isEmpty, s"The following events happened, that should NOT have happened: ${actualUnexpectedEvents.mkString}")
    }
  }

  @varargs def assertEventsHappened(expectedEvents: Class[_]*): RecipeAssert = assertEventNamesHappened(expectedEvents.map(_.getSimpleName):_*)
  @varargs def assertEventsNotHappened(forbiddenEvent: Class[_]*): RecipeAssert = assertEventNamesNotHappened(forbiddenEvent.map(_.getSimpleName):_*)

  def assertIngredient(name: String) = new IngredientAssert(name)

  // logging

  def logIngredients(): RecipeAssert = {
    await(baker.getIngredients(recipeInstanceId).map(ingredients => logger.info(s"Ingredients: $ingredients"))).get
    this
  }

  def logEventNames(): RecipeAssert = {
    await(baker.getEventNames(recipeInstanceId).map(names => logger.info(s"Event names: $names"))).get
    this
  }

  def logVisualState(): RecipeAssert = {
    val visualStateRecipeFuture = baker.getVisualState(recipeInstanceId).map(state => logger.info(s"Visual state: $state"))
    Await.result(visualStateRecipeFuture, 60.seconds)
    this
  }

  def logCurrentState(): RecipeAssert = {
    logEventNames()
    logIngredients()
    logVisualState()
  }

  // private helper functions

  private def await[T](future: Future[T]): Try[T] =
    Try(Await.result(future, timeout))

  private def verify(future: Future[_]): RecipeAssert = await(future) match {
    case Success(_) => this
    case Failure(exception) =>
      Try(logCurrentState())
      exception match {
        case e: ExecutionException => throw e.getCause
        case _ => throw exception
      }
  }

  private def getActualFlow: Future[EventsFlow] =
    baker.getEvents(recipeInstanceId).map(events => EventsFlow(events.map(_.name).toSet))

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

  class IngredientAssert(name: String) {

    def isNull: RecipeAssert =
      is(value => assert(value.isNull, s"expect value '$value' to be null"))

    def isAbsent: RecipeAssert =
      is(value => assert(value == null, s"expect value to be absent"))

    def isEqual(expected: Any): RecipeAssert =
      is(value => assert(value.equalsObject(expected), s"expect value '$value' to be equal to '$expected'"))

    def is(assertion: Consumer[Value]): RecipeAssert = verify {
      baker.getIngredients(recipeInstanceId).map(ingredients => assertion.accept(ingredients.getOrElse(name, null)))
    }
  }
}

object RecipeAssert {
  val DEFAULT_TIMEOUT: Duration = 10 seconds

  def apply(baker: Baker, recipeInstanceId: String, timeout: Duration = DEFAULT_TIMEOUT) =
    new RecipeAssert(baker, recipeInstanceId, timeout)

  def of(baker: javadsl.Baker, recipeInstanceId: String): RecipeAssert =
    apply(baker, recipeInstanceId)

  def of(baker: javadsl.Baker, recipeInstanceId: String, timeout: java.time.Duration): RecipeAssert =
    apply(baker, recipeInstanceId, timeout)

  private implicit def toScala(duration: java.time.Duration): Duration =
    Duration.fromNanos(duration.toNanos)

  private implicit def toScala(baker: javadsl.Baker): scaladsl.Baker = {
    baker.getScalaBaker
  }
}
