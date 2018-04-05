package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

case class InteractionCompleted(timeStamp: Long, processId: String, interactionName: String, event: RuntimeEvent) extends BakerEvent
