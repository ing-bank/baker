package com.ing.baker.runtime.core.events

case class InteractionFailed(timeStamp: Long,
                             duration: Long,
                             recipeName: String,
                             processId: String,
                             interactionName: String,
                             throwable: Throwable) extends BakerEvent
