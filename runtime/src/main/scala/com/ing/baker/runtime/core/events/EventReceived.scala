package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

case class EventReceived(timeStamp: Long, processId: String, correlationId: Option[String], event: RuntimeEvent) extends BakerEvent
