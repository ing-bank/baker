package com.ing.baker.runtime.core.events

import com.ing.baker.runtime.core.RuntimeEvent

/**
  * Event describing the fact that an interaction was executed successfully
  *
  * @param timeStamp The time that the execution ended
  * @param duration The duration of the execution time
  * @param recipeName The name of the recipe that interaction is part of
  * @param processId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param event The event that was produced as a result of the execution
  */
case class InteractionCompleted(timeStamp: Long,
                                duration: Long,
                                recipeName: String,
                                processId: String,
                                interactionName: String,
                                event: RuntimeEvent) extends BakerEvent
