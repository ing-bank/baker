package com.ing.baker.runtime.core

object SensoryEventStatus {
  sealed trait SensoryEventStatus
  case object Received extends SensoryEventStatus
  case object Completed extends SensoryEventStatus
  case object FiringLimitMet extends SensoryEventStatus
}
