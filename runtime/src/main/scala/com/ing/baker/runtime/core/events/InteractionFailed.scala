package com.ing.baker.runtime.core.events

/**
  * Event describing the fact that an interaction was executed successfully
  *
  * @param timeStamp The time that the execution ended
  * @param duration The duration of the execution time
  * @param recipeName The name of the recipe that interaction is part of
  * @param processId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param throwable The exception that was thrown by the interaction
  */
case class InteractionFailed(timeStamp: Long,
                             duration: Long,
                             recipeName: String,
                             processId: String,
                             interactionName: String,
                             throwable: Throwable) extends BakerEvent
