package com.ing.baker.runtime.model.recipeinstance.modules

import cats.data.{State, StateT}
import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, TransitionExecution, TransitionExecutionOutcome}
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment}

trait RecipeInstanceStateMutations { recipeInstance: RecipeInstance with RecipeInstanceComplexProperties =>

  def addExecution(execution: TransitionExecution*): RecipeInstance = {
    val addedExecutions = recipeInstance.executions ++ execution.map(e => e.id -> e).toMap
    recipeInstance.copy(executions = addedExecutions)
  }

  def aggregateOutputEvent(event: Option[EventInstance]): RecipeInstance = {
      event match {
        case None =>recipeInstance
        case Some(outputEvent) =>
          recipeInstance.copy(
            ingredients = recipeInstance.ingredients ++ outputEvent.providedIngredients,
            events = recipeInstance.events :+ EventMoment(outputEvent.name, System.currentTimeMillis()))
      }
  }

  def recordExecutionOutcome(outcome: TransitionExecutionOutcome): RecipeInstance =
      outcome match {
        case event: TransitionExecutionOutcome.Completed =>
          val newState = aggregateOutputEvent(event.output)
          val consumed: Marking[Place] = unmarshallMarking(recipeInstance.recipe.petriNet.places, event.consumed)
          val produced: Marking[Place] = unmarshallMarking(recipeInstance.recipe.petriNet.places, event.produced)
          newState.copy(
            sequenceNumber = recipeInstance.sequenceNumber + 1,
            marking = (recipeInstance.marking |-| consumed) |+| produced,
            receivedCorrelationIds = recipeInstance.receivedCorrelationIds ++ event.correlationId,
            executions = recipeInstance.executions - event.transitionExecutionId
          )
        case event: TransitionExecutionOutcome.Failed =>
          val transition = transitionById(event.transitionId)
          val consumed: Marking[Place] = unmarshallMarking(recipeInstance.recipe.petriNet.places, event.consume)
          lazy val newExecutionState =
            TransitionExecution(
              id = event.transitionExecutionId,
              recipeInstanceId = recipeInstance.recipeInstanceId,
              recipe = recipeInstance.recipe,
              transition = transition,
              consume = consumed,
              input = event.input,
              ingredients = recipeInstance.ingredients,
              correlationId = event.correlationId)
          val originalExecution = recipeInstance.executions.getOrElse(event.transitionExecutionId, newExecutionState)
          val updatedExecution = originalExecution.copy(state =
            TransitionExecution.State.Failed(event.timeFailed, originalExecution.failureCount + 1, event.failureReason, event.exceptionStrategy))
          addExecution(updatedExecution)
    }

}
