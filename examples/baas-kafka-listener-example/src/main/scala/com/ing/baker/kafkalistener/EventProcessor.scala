package com.ing.baker.kafkalistener

import com.ing.baker.runtime.common.{BakerEvent, EventInstance}

trait EventProcessor {

  def bakerEvent(event: BakerEvent)

  def recipeEvent(event: EventInstance)

  def parseFailure(serialized: String, error: String)

}
