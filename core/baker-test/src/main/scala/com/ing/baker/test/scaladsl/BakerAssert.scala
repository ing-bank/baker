package com.ing.baker.test.scaladsl

import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.test.common

import scala.concurrent.duration._
import scala.language.postfixOps

class BakerAssert(_baker: Baker, _recipeInstanceId: String, _timeout: Duration) extends common.BakerAssert[BakerEventsFlow] {
  override protected def baker: Baker = _baker

  override protected def recipeInstanceId: String = _recipeInstanceId

  override protected def timeout: Duration = _timeout;
}

object BakerAssert {
  def apply(baker: Baker, recipeInstanceId: String, timeout: Duration = common.BakerAssert.DEFAULT_TIMEOUT): BakerAssert =
    new BakerAssert(baker, recipeInstanceId, timeout)
}
