package com.ing.baker.runtime.core.events

import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome

/**
  * Event describing the fact that an interaction failed during execution
  *
  * @param timeStamp The time that the execution ended
  * @param duration The duration of the execution time
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param processId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param failureCount The number of times that this interaction execution failed
  * @param throwable The exception that was thrown by the interaction
  * @param exceptionStrategyOutcome The strategy that was applied as a result of the failure
  */
case class InteractionFailed(timeStamp: Long,
                             duration: Long,
                             recipeName: String,
                             recipeId: String,
                             processId: String,
                             interactionName: String,
                             failureCount: Int,
                             throwable: Throwable,
                             exceptionStrategyOutcome: ExceptionStrategyOutcome) extends BakerEvent
