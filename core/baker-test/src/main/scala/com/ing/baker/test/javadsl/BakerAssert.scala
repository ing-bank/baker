package com.ing.baker.test.javadsl

import java.time.Duration

import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.test.common

import scala.concurrent.duration

class BakerAssert(
                   private val _baker: javadsl.Baker,
                   private val _recipeInstanceId: String,
                   private val _timeout: Duration)
  extends common.BakerAssert[BakerEventsFlow] {

  override protected def baker: Baker = toScalaBaker(_baker)

  override protected def recipeInstanceId: String = _recipeInstanceId

  override protected def timeout: duration.Duration = scala.concurrent.duration.Duration.fromNanos(_timeout.toNanos)

  // hack for now as there is no way to convert java baker to scala baker
  private def toScalaBaker(baker: javadsl.Baker): Baker = {
    val field = classOf[javadsl.Baker].getDeclaredField("baker")
    try {
      field.setAccessible(true)
      field.get(baker).asInstanceOf[Baker]
    } finally {
      field.setAccessible(true)
    }
  }
}

object BakerAssert {
  def apply(baker: javadsl.Baker,
            recipeInstanceId: String,
            timeout: Duration = Duration.ofSeconds(common.BakerAssert.DEFAULT_TIMEOUT.toSeconds)): BakerAssert = {
    new BakerAssert(baker, recipeInstanceId, timeout)
  }

  def of(baker: javadsl.Baker,
         recipeInstanceId: String): BakerAssert = apply(baker, recipeInstanceId)
}
