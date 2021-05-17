package com.ing.bakery.baker

import scala.concurrent.Future

object BakerReadinessCheck {
  var ready: Boolean = false
  def enable(): Unit = { BakerReadinessCheck.ready = true }
}

class BakerReadinessCheck extends (() => Future[Boolean]) {
  override def apply(): Future[Boolean] = Future.successful(BakerReadinessCheck.ready)
}
