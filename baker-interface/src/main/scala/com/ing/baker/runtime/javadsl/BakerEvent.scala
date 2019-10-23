package com.ing.baker.runtime.javadsl

import java.util.Optional

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

sealed trait BakerEvent extends common.BakerEvent with JavaApi {
  type Event = EventInstance

//  def asJava(): = this match {
//    case EventReceived(timeStamp, recipeName, recipeId, RecipeInstanceId, correlationId, event)
//  }
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
                         correlationId: Optional[String],
                         event: EventInstance) extends BakerEvent with common.EventReceived {

  def getTimeStamp: Long = timeStamp

  def getRecipeName: String = recipeName

  def getRecipeId: String = recipeId

  def getRecipeInstanceId: String = recipeInstanceId

  def getCorrelationId: Optional[String] = correlationId

  def getEvent: EventInstance = event
}

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
                         correlationId: Optional[String],
                         event: EventInstance,
                         reason: RejectReason) extends BakerEvent with common.EventRejected {

  def getTimeStamp: Long = timeStamp

  def getRecipeInstanceId: String = recipeInstanceId

  def getCorrelationId: Optional[String] = correlationId

  def getEvent: EventInstance = event

  def getReason: RejectReason = reason
}
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
                             exceptionStrategyOutcome: ExceptionStrategyOutcome) extends BakerEvent with common.InteractionFailed {

  def getTimeStamp: Long = timeStamp

  def getDuration: Long = duration

  def getRecipeName: String = recipeName

  def getRecipeId: String = recipeId

  def getRecipeInstanceId: String = recipeInstanceId

  def getInteractionName: String = interactionName

  def getFailureCount: Int = failureCount

  def getThrowable: Throwable = throwable

  def getExceptionStrategyOutcome: ExceptionStrategyOutcome = exceptionStrategyOutcome
}

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
                              interactionName: String) extends BakerEvent with common.InteractionStarted {

  def getTimeStamp: Long = timeStamp

  def getRecipeName: String = recipeName

  def getRecipeId: String = recipeId

  def getRecipeInstanceId: String = recipeInstanceId

  def getInteractionName: String = interactionName
}

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
                                event: Optional[EventInstance]) extends BakerEvent with common.InteractionCompleted {

  def getTimeStamp: Long = timeStamp

  def getDuration: Long = duration

  def getRecipeName: String = recipeName

  def getRecipeId: String = recipeId

  def getRecipeInstanceId: String = recipeInstanceId

  def getInteractionName: String = interactionName

  def getEvent: Optional[EventInstance] = event
}

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
                                 recipeInstanceId: String) extends BakerEvent with common.RecipeInstanceCreated {

  def getTimeStamp: Long = timeStamp

  def getRecipeId: String = recipeId

  def getRecipeName: String = recipeName

  def getRecipeInstanceId: String = recipeInstanceId
}

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
                       compiledRecipe: CompiledRecipe) extends BakerEvent with common.RecipeAdded {

  def getRecipeName: String = recipeName

  def getRecipeId: String = recipeId

  def getData: Long = date

  def getCompiledRecipe: CompiledRecipe = compiledRecipe
}

