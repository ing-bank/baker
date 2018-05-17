package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

case class InteractionCompleted(timeStamp: Long,
                                duration: Long,
                                recipeName: String,
                                processId: String,
                                interactionName: String,
                                event: RuntimeEvent) extends BakerEvent
