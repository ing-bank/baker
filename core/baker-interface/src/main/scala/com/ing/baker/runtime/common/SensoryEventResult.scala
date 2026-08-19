package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

@deprecated("The SensoryEventResult class will be removed after December 2026. Use fireSensoryEventAndAwaitReceived -> awaitCompleted -> getIngredients + getEventNames instead.", "5.1.0")
trait SensoryEventResult extends LanguageApi {

  def sensoryEventStatus: SensoryEventStatus

  def eventNames: language.Seq[String]

  def ingredients: language.Map[String, Value]
}

