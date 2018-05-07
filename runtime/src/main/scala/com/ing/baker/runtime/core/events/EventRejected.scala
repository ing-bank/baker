package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

case class EventRejected(timeStamp: Long,
                         processId: String,
                         correlationId: Option[String],
                         event: RuntimeEvent,
                         reason: RejectReason) extends BakerEvent
