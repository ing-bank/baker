package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

/**
  * Event describing the fact that an event was received for a process.
  *
  * @param timeStamp The time that the event was received
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param processId The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event The event
  */
case class EventReceived(timeStamp: Long,
                         recipeName: String,
                         recipeId: String,
                         processId: String,
                         correlationId: Option[String],
                         event: RuntimeEvent) extends BakerEvent
