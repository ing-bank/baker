package com.ing.baker.runtime.scaladsl


import java.util.Optional

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.{common, javadsl}

sealed trait BakerEvent extends common.BakerEvent with ScalaApi {
  type Event = EventInstance

  def asJava: javadsl.BakerEvent = this match {
    case EventReceived(timeStamp, recipeName, recipeId, recipeInstanceId, correlationId, event) =>
      javadsl.EventReceived(timeStamp, recipeName, recipeId, recipeInstanceId, Optional.ofNullable(correlationId.orNull), event.asJava)
    case EventRejected(timeStamp, recipeInstanceId, correlationId, event, reason) =>
      javadsl.EventRejected(timeStamp, recipeInstanceId, Optional.ofNullable(correlationId.orNull), event.asJava, reason)
    case InteractionFailed(timeStamp, duration, recipeName, recipeId, recipeInstanceId, interactionName, failureCount, throwable, exceptionStrategyOutcome) =>
      javadsl.InteractionFailed(timeStamp, duration, recipeName, recipeId, recipeInstanceId, interactionName, failureCount, throwable, exceptionStrategyOutcome)
    case InteractionStarted(timeStamp, recipeName, recipeId, recipeInstanceId, interactionName) =>
      javadsl.InteractionStarted(timeStamp, recipeName, recipeId, recipeInstanceId, interactionName)
    case InteractionCompleted(timeStamp, duration, recipeName, recipeId, recipeInstanceId, interactionName, event) =>
      javadsl.InteractionCompleted(timeStamp, duration, recipeName, recipeId, recipeInstanceId, interactionName, Optional.ofNullable(event.map(_.asJava).orNull))
    case RecipeInstanceCreated(timeStamp, recipeId, recipeName, recipeInstanceId) =>
      javadsl.RecipeInstanceCreated(timeStamp, recipeId, recipeName, recipeInstanceId)
    case RecipeAdded(recipeName, recipeId, date, compiledRecipe) =>
      javadsl.RecipeAdded(recipeName, recipeId, date, compiledRecipe)
  }
}

/**
  * Event describing the fact that an event was received for a process.
  *
  * @param timeStamp The time that the event was received
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param recipeInstanceId The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event The event
  */
case class EventReceived(timeStamp: Long,
                         recipeName: String,
                         recipeId: String,
                         recipeInstanceId: String,
                         correlationId: Option[String],
                         event: EventInstance) extends BakerEvent with common.EventReceived

/**
  * Event describing the fact that an event was received but rejected for a process
  *
  * @param timeStamp The time that the event was received
  * @param recipeInstanceId The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event The event
  * @param reason The reason that the event was rejected
  */
case class EventRejected(timeStamp: Long,
                         recipeInstanceId: String,
                         correlationId: Option[String],
                         event: EventInstance,
                         reason: RejectReason) extends BakerEvent with common.EventRejected
/**
  * Event describing the fact that an interaction failed during execution
  *
  * @param timeStamp The time that the execution ended
  * @param duration The duration of the execution time
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param recipeInstanceId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param failureCount The number of times that this interaction execution failed
  * @param throwable The exception that was thrown by the interaction
  * @param exceptionStrategyOutcome The strategy that was applied as a result of the failure
  */
case class InteractionFailed(timeStamp: Long,
                             duration: Long,
                             recipeName: String,
                             recipeId: String,
                             recipeInstanceId: String,
                             interactionName: String,
                             failureCount: Int,
                             throwable: Throwable,
                             exceptionStrategyOutcome: ExceptionStrategyOutcome) extends BakerEvent with common.InteractionFailed

/**
  * Event describing the fact that an interaction has started executing
  *
  * @param timeStamp The time that the execution started
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param recipeInstanceId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  */
case class InteractionStarted(timeStamp: Long,
                              recipeName: String,
                              recipeId: String,
                              recipeInstanceId: String,
                              interactionName: String) extends BakerEvent with common.InteractionStarted

/**
  * Event describing the fact that an interaction was executed successfully
  *
  * @param timeStamp The time that the execution ended
  * @param duration The duration of the execution time
  * @param recipeName The name of the recipe that interaction is part of
  * @param recipeId The recipe id
  * @param recipeInstanceId The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param event The event that was produced as a result of the execution
  */

case class InteractionCompleted(timeStamp: Long,
                                duration: Long,
                                recipeName: String,
                                recipeId: String,
                                recipeInstanceId: String,
                                interactionName: String,
                                event: Option[EventInstance]) extends BakerEvent with common.InteractionCompleted

/**
  * Event describing the fact that a baker process was created
  *
  * @param timeStamp The time the process was created
  * @param recipeId The recipe id
  * @param recipeName The name of the recipe
  * @param recipeInstanceId The process id
  */
case class RecipeInstanceCreated(timeStamp: Long,
                                 recipeId: String,
                                 recipeName: String,
                                 recipeInstanceId: String) extends BakerEvent with common.RecipeInstanceCreated

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
                       compiledRecipe: CompiledRecipe) extends BakerEvent with common.RecipeAdded

