package com.ing.baker.runtime.akka.events

import java.util.Optional

import akka.actor.NoSerializationVerificationNeeded
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.scaladsl.RuntimeEvent

sealed trait BakerEvent extends NoSerializationVerificationNeeded

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

/**
  * Event describing the fact that an event was received but rejected for a process
  *
  * @param timeStamp The time that the event was received
  * @param processId The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event The event
  * @param reason The reason that the event was rejected
  */
case class EventRejected(timeStamp: Long,
                         processId: String,
                         correlationId: Option[String],
                         event: RuntimeEvent,
                         reason: RejectReason) extends BakerEvent
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

/**
  * Event describing the fact that an interaction has started executing
  *
  * @param timeStamp The time that the execution started
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param processId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  */
case class InteractionStarted(timeStamp: Long,
                              recipeName: String,
                              recipeId: String,
                              processId: String,
                              interactionName: String) extends BakerEvent

/**
  * Event describing the fact that an interaction was executed successfully
  *
  * @param timeStamp The time that the execution ended
  * @param duration The duration of the execution time
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param processId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param event The event that was produced as a result of the execution
  */

case class InteractionCompleted(timeStamp: Long,
                                duration: Long,
                                recipeName: String,
                                recipeId: String,
                                processId: String,
                                interactionName: String,
                                event: Option[RuntimeEvent]) extends BakerEvent {
  /**
    * Java Optional version of the event.
    *
    * @return The (optional) event output of the interaction.
    */
  def getEvent: Optional[RuntimeEvent] =
    event.map(e => Optional.of(e)).getOrElse(Optional.empty())
}

/**
  * Event describing the fact that a baker process was created
  *
  * @param timeStamp The time the process was created
  * @param recipeId The recipe id
  * @param recipeName The name of the recipe
  * @param processId The process id
  */
case class ProcessCreated(timeStamp: Long,
                          recipeId: String,
                          recipeName: String,
                          processId: String) extends BakerEvent

/**
  * An event describing the fact that a recipe was added to baker.
  *
  * @param recipeName The name of the recipe
  * @param recipeId The id of the recipe
  * @param date The time the recipe was added to baker
  */
case class RecipeAdded(recipeName: String,
                       recipeId: String,
                       date: Long,
                       compiledRecipe: CompiledRecipe) extends BakerEvent

