package com.ing.baker.runtime.akka

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.types.Value

case class SensoryEventResult(
  status: SensoryEventStatus,
  events: Seq[String],
  ingredients: Map[String, Value]
) extends common.SensoryEventResult[Seq, Map]


