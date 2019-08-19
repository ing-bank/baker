package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

trait SensoryEventResult extends LanguageApi {

  def sensoryEventStatus: SensoryEventStatus

  def eventNames: language.Seq[String]

  def ingredients: language.Map[String, Value]
}

