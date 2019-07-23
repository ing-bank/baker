package com.ing.baker.runtime.common

import akka.actor.NoSerializationVerificationNeeded
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

// TODO: rename subtypes of BakerEvent to resamble the new names
trait BakerEvent extends LanguageApi with NoSerializationVerificationNeeded {
  self =>
  type Event <: EventInstance {type Language <: self.Language}
}

/**
  * Event describing the fact that an event was received for a process.
  *
  * @param timeStamp     The time that the event was received
  * @param recipeName    The name of the recipe that interaction is part of
  * @param recipeId      The recipe id
  * @param recipeInstanceId     The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event         The event
  */
trait EventReceived extends BakerEvent {
  val timeStamp: Long
  val recipeName: String
  val recipeId: String
  val recipeInstanceId: String
  val correlationId: language.Option[String]
  val event: Event
}

/**
  * Event describing the fact that an event was received but rejected for a process
  *
  * @param timeStamp     The time that the event was received
  * @param recipeInstanceId     The id of the process
  * @param correlationId The (optional) correlation id of the event
  * @param event         The event
  * @param reason        The reason that the event was rejected
  */
trait EventRejected extends BakerEvent {
  val timeStamp: Long
  val recipeInstanceId: String
  val correlationId: language.Option[String]
  val event: Event
  val reason: RejectReason
}

/**
  * Event describing the fact that an interaction failed during execution
  *
  * @param timeStamp                The time that the execution ended
  * @param duration                 The duration of the execution time
  * @param recipeName               The name of the recipe that interaction is part of
  * @param recipeId                 The recipe id
  * @param recipeInstanceId                The id of the process the interaction is executed for
  * @param interactionName          The name of the interaction
  * @param failureCount             The number of times that this interaction execution failed
  * @param throwable                The exception that was thrown by the interaction
  * @param exceptionStrategyOutcome The strategy that was applied as a result of the failure
  */
trait InteractionFailed extends BakerEvent {
  val timeStamp: Long
  val duration: Long
  val recipeName: String
  val recipeId: String
  val recipeInstanceId: String
  val interactionName: String
  val failureCount: Int
  val throwable: Throwable
  val exceptionStrategyOutcome: ExceptionStrategyOutcome
}

/**
  * Event describing the fact that an interaction has started executing
  *
  * @param timeStamp       The time that the execution started
  * @param recipeName      The name of the recipe that interaction is part of
  * @param recipeId        The recipe id
  * @param recipeInstanceId       The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  */
trait InteractionStarted extends BakerEvent {
  val timeStamp: Long
  val recipeName: String
  val recipeId: String
  val recipeInstanceId: String
  val interactionName: String
}

/**
  * Event describing the fact that an interaction was executed successfully
  *
  * @param timeStamp       The time that the execution ended
  * @param duration        The duration of the execution time
  * @param recipeName      The name of the recipe that interaction is part of
  * @param recipeId        The recipe id
  * @param recipeInstanceId       The id of the process the interaction is executed for
  * @param interactionName The name of the interaction
  * @param event           The event that was produced as a result of the execution
  */

trait InteractionCompleted extends BakerEvent {
  val timeStamp: Long
  val duration: Long
  val recipeName: String
  val recipeId: String
  val recipeInstanceId: String
  val interactionName: String
  val event: language.Option[Event]
}

/**
  * Event describing the fact that a baker process was created
  *
  * @param timeStamp  The time the process was created
  * @param recipeId   The recipe id
  * @param recipeName The name of the recipe
  * @param recipeInstanceId  The process id
  */
trait ProcessCreated extends BakerEvent {
  val timeStamp: Long
  val recipeId: String
  val recipeName: String
  val recipeInstanceId: String
}

/**
  * An event describing the fact that a recipe was added to baker.
  *
  * @param recipeName The name of the recipe
  * @param recipeId   The id of the recipe
  * @param date       The time the recipe was added to baker
  */
trait RecipeAdded extends BakerEvent {
  val recipeName: String
  val recipeId: String
  val date: Long
  val compiledRecipe: CompiledRecipe
}

