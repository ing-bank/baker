package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.types.Value
import scala.collection.immutable.Seq

case class SensoryEventResult(
                               sensoryEventStatus: SensoryEventStatus,
                               eventNames: Seq[String],
                               ingredients: Map[String, Value]
) extends common.SensoryEventResult with ScalaApi
