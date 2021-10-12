package com.ing.baker.test

import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.language.postfixOps

class BakerAsync(private val baker: Baker) {

  /**
    * Returns the future that waits on the given events
    * for the specific recipe instance to be available.
    *
    * Events check is done in 100 millis intervals as the
    * Baker's event listener implementation has issues:
    * - event listener cannot be unregistered
    * - event listener fires before an event becomes available through `getEventNames`
    */
  def waitFor(recipeInstanceId: String, events: Set[String]): Future[Unit] = for {
    check <- checkEvents(recipeInstanceId, events)
    _ <- if (check) Future.successful(()) else Future(Thread.`yield`())
    next <- if (check) Future.successful(()) else waitFor(recipeInstanceId, events)
  } yield next

  private def checkEvents(recipeInstanceId: String, expected: Set[String]): Future[Boolean] =
    baker.getEventNames(recipeInstanceId).map(actual => expected.subsetOf(actual.toSet))
}