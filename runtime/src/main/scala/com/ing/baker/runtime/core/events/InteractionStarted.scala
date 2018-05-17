package com.ing.baker.runtime.core.events

case class InteractionStarted(timeStamp: Long,
                              recipeName: String,
                              processId: String,
                              interactionName: String) extends BakerEvent
