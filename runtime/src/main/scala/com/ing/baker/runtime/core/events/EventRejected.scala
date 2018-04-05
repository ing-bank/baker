package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

sealed trait RejectReason

case object ProcessDeleted
case object AlreadReceived
case object ReceivePeriodExpired
case object InvalidEvent

case class EventRejected(timeStamp: Long, processId: String, correlationId: Option[String], event: RuntimeEvent, reason: RejectReason)
