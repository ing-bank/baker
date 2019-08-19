package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

case class SensoryEventResult(
                               sensoryEventStatus: SensoryEventStatus,
                               eventNames: java.util.List[String],
                               ingredients: java.util.Map[String, Value]
) extends common.SensoryEventResult with JavaApi {

  def getSensoryEventState: SensoryEventStatus = sensoryEventStatus

  def getEventName: java.util.List[String] = eventNames

  def getIngredients: java.util.Map[String, Value] = ingredients
}
