package com.ing.baker.runtime.core.events

case class InteractionFailed(timeStamp: Long,
                             duration: Long,
                             processId: String,
                             interactionName: String,
                             throwable: Throwable) extends BakerEvent
