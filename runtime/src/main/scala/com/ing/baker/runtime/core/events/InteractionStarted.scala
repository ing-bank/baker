package com.ing.baker.runtime.core.events

case class InteractionStarted(timeStamp: Long,
                              processId: String,
                              interactionName: String) extends BakerEvent
