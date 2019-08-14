package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.types.Value

case class EventResult(
  status: SensoryEventStatus,
  events: Seq[String],
  ingredients: Map[String, Value]
) extends common.EventResult with ScalaApi
