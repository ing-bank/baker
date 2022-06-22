package com.ing.baker.kafkalistener

import com.ing.baker.runtime.common.{BakerEvent, EventInstance}

trait EventProcessor {

  def bakerEvent(event: BakerEvent): Unit

  def recipeEvent(event: EventInstance): Unit

  def parseFailure(serialized: String, error: String): Unit

}
