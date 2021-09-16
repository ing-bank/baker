package com.ing.baker.test

import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.language.postfixOps

class BakerAsync(private val baker: Baker) {

  def waitFor(recipeInstanceId: String, events: Set[String]): Future[Unit] = {
    for {
      cont <- checkEvents(recipeInstanceId, events)
      next <- if (cont) Future.successful(()) else waitFor(recipeInstanceId, events)
    } yield next
  }

  private def checkEvents(recipeInstanceId: String, expected: Set[String]): Future[Boolean] =
    baker.getEventNames(recipeInstanceId).map(actual => expected.subsetOf(actual.toSet))
}