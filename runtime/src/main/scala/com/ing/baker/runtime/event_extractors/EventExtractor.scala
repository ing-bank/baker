package com.ing.baker.runtime.event_extractors

import com.ing.baker.runtime.core.RuntimeEvent

/**
  * Extracts ingredients from an object.
  */
trait EventExtractor {

  /**
    * Extracts the ingredient data from a given object.
    *
    * @param obj The object.
    *
    * @return The ingredient data.
    */
  def extractEvent(obj: Any): RuntimeEvent
}

