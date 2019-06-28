package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

class EventResult(
  val status: SensoryEventStatus,
  val events: java.util.List[String],
  val ingredients: java.util.Map[String, Value]
) extends common.EventResult with JavaApi
