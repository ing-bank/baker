package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

sealed trait RejectReason

case object NoSuchProcess extends RejectReason
case object ProcessDeleted extends RejectReason
case object AlreadReceived extends RejectReason
case object ReceivePeriodExpired extends RejectReason
case object FiringLimitMet extends RejectReason
case object InvalidEvent extends RejectReason

case class EventRejected(timeStamp: Long, processId: String, correlationId: Option[String], event: RuntimeEvent, reason: RejectReason) extends BakerEvent
