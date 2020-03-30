package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.serialization.CirceExtensions.{Formatter, deriveObjectFormatter}

object BakerEventFormatters {

  implicit val bakerEventFormatter: Formatter[BakerEvent] = deriveObjectFormatter[BakerEvent]
}