package com.ing.baker.runtime.model.recipeinstance.modules

import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, TransitionExecution, TransitionExecutionOutcome}
import com.ing.baker.runtime.scaladsl.EventMoment

trait RecipeInstanceStateMutations { recipeInstance: RecipeInstance with RecipeInstanceComplexProperties =>

  def addExecution(execution: TransitionExecution*): RecipeInstance =
    recipeInstance.copy(executions = recipeInstance.executions ++ execution.map(e => e.id -> e).toMap)

  def recordExecutionOutcome(outcome: TransitionExecutionOutcome): RecipeInstance =
    outcome match {

      case completedOutcome: TransitionExecutionOutcome.Completed =>
        recipeInstance
          .aggregateOutputEvent(completedOutcome)
          .increaseSequenceNumber
          .aggregatePetriNetChanges(completedOutcome)
          .addReceivedCorrelationId(completedOutcome)
          .removeExecution(completedOutcome)

      case failedOutcome: TransitionExecutionOutcome.Failed =>
        transitionExecutionToFailedState(failedOutcome)
    }

  private def transitionExecutionToFailedState(failedOutcome: TransitionExecutionOutcome.Failed): RecipeInstance = {
    val transition = recipeInstance.transitionById(failedOutcome.transitionId)
    val consumed: Marking[Place] = unmarshallMarking(recipeInstance.petriNet.places, failedOutcome.consume)
    lazy val newExecutionState =
      TransitionExecution(
        id = failedOutcome.transitionExecutionId,
        recipeInstanceId = recipeInstance.recipeInstanceId,
        recipe = recipeInstance.recipe,
        transition = transition,
        consume = consumed,
        input = failedOutcome.input,
        ingredients = recipeInstance.ingredients,
        correlationId = failedOutcome.correlationId)
    val originalExecution = recipeInstance.executions.getOrElse(failedOutcome.transitionExecutionId, newExecutionState)
    val updatedExecution = originalExecution.copy(state =
      TransitionExecution.State.Failed(failedOutcome.timeFailed, originalExecution.failureCount + 1, failedOutcome.failureReason, failedOutcome.exceptionStrategy))
    addExecution(updatedExecution)
  }

  private def removeExecution(outcome: TransitionExecutionOutcome.Completed): RecipeInstance =
    recipeInstance.copy(executions = recipeInstance.executions - outcome.transitionExecutionId)

  private def aggregateOutputEvent(outcome: TransitionExecutionOutcome.Completed): RecipeInstance = {
      outcome.output match {
        case None =>recipeInstance
        case Some(outputEvent) =>
          recipeInstance.copy(
            ingredients = recipeInstance.ingredients ++ outputEvent.providedIngredients,
            events = recipeInstance.events :+ EventMoment(outputEvent.name, System.currentTimeMillis()))
      }
  }

  private def increaseSequenceNumber: RecipeInstance =
    recipeInstance.copy(sequenceNumber = recipeInstance.sequenceNumber + 1)

  private def aggregatePetriNetChanges(outcome: TransitionExecutionOutcome.Completed): RecipeInstance = {
    val consumed: Marking[Place] = unmarshallMarking(recipeInstance.petriNet.places, outcome.consumed)
    val produced: Marking[Place] = unmarshallMarking(recipeInstance.petriNet.places, outcome.produced)
    recipeInstance.copy(marking = (recipeInstance.marking |-| consumed) |+| produced)
  }

  private def addReceivedCorrelationId(outcome: TransitionExecutionOutcome.Completed): RecipeInstance =
    recipeInstance.copy(receivedCorrelationIds = recipeInstance.receivedCorrelationIds ++ outcome.correlationId)
}
