package com.ing.bakery.components

import scala.concurrent.Future

object BakerReadinessCheck {
  var ready: Boolean = false
  def enable(): Unit = { BakerReadinessCheck.ready = true }
}

class BakerReadinessCheck extends (() => Future[Boolean]) {
  override def apply(): Future[Boolean] = Future.successful(BakerReadinessCheck.ready)
}
