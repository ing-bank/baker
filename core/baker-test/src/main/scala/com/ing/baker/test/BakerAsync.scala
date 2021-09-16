package com.ing.baker.test

import com.ing.baker.runtime.scaladsl.Baker
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.language.postfixOps

class BakerAsync(private val baker: Baker) extends LazyLogging {

  def waitFor(recipeInstanceId: String, events: Set[String], timeout: Duration = 10 seconds): Unit = {
    Await.result(waitEvents(recipeInstanceId, events), timeout)
  }

  private def waitEvents(recipeInstanceId: String, events: Set[String]): Future[Unit] = {
    for {
      cont <- checkEvents(recipeInstanceId, events)
      next <- if (cont) Future.successful(()) else waitEvents(recipeInstanceId, events)
    } yield next
  }

  private def checkEvents(recipeInstanceId: String, expected: Set[String]): Future[Boolean] =
    baker.getEventNames(recipeInstanceId).map(actual => expected.subsetOf(actual.toSet))
}