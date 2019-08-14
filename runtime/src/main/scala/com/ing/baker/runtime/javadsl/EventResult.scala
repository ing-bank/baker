package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

case class EventResult(
  status: SensoryEventStatus,
  events: java.util.List[String],
  ingredients: java.util.Map[String, Value]
) extends common.EventResult with JavaApi
