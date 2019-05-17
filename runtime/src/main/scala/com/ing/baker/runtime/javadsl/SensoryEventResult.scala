package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.common
import com.ing.baker.types.Value

class SensoryEventResult(
  val status: SensoryEventStatus,
  val events: java.util.List[String],
  val ingredients: java.util.Map[String, Value]
) extends common.SensoryEventResult[java.util.List, java.util.Map]
