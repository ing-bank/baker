package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

/**
  * Event describing the fact that an event was received but rejected for a process
  *
  * @param timeStamp The time that the event was received
  * @param processId The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event The event
  * @param reason The reason that the event was rejected
  */
case class EventRejected(timeStamp: Long,
                         processId: String,
                         correlationId: Option[String],
                         event: RuntimeEvent,
                         reason: RejectReason) extends BakerEvent
