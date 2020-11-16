package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api.{Marking, MultiSet}
import com.ing.baker.runtime.model.recipeinstance.execution.TransitionExecution
import com.ing.baker.runtime.scaladsl.EventMoment
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api._
import com.ing.baker.types.Value

case class RecipeInstanceState(
                                recipeInstanceId: String,
                                recipe: CompiledRecipe,
                                createdOn: Long,
                                sequenceNumber: Long,
                                marking: Marking[Place],
                                ingredients: Map[String, Value],
                                events: List[EventMoment],
                                receivedCorrelationIds: Set[String],
                                executions: Map[Long, TransitionExecution]
                              ) extends RecipeInstanceEventValidation {

  def activeExecutions: Iterable[TransitionExecution] =
    executions.values.filter(_.isActive)

  def getInteractionExecution(interactionName: String): Option[(InteractionTransition, TransitionExecution)] =
    for {
      transition <- recipe.interactionTransitions.find(_.interactionName == interactionName)
      transitionExecution <- executions.collectFirst {
        case (_, execution) if execution.transition.id == transition.id =>
          execution
      }
    } yield (transition, transitionExecution)

  def sensoryEventByName(name: String): Option[EventDescriptor] =
    recipe.sensoryEvents.find(_.name == name)

  def allMarking: Marking[Place] =
    marking

  /** The marking that is already used by running jobs */
  def reservedMarkings: Marking[Place] =
    executions
      .map { case (_, execution) ⇒ execution.consume }
      .reduceOption(_ |+| _)
      .getOrElse(Marking.empty)

  /** Markings that are available for an execution. */
  def availableMarkings: Marking[Place] =
    allMarking |-| reservedMarkings

  def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {

    def consumableTokens(p: Place, ofMarking: Marking[Place]): MultiSet[Any] =
      ofMarking.getOrElse(p, MultiSet.empty)

    // TODO this is not the most efficient, should break early when consumable tokens < edge weight
    val consumable = recipe.petriNet.inMarking(t).map {
      case (place, count) ⇒ (place, count, consumableTokens(place, ofMarking))
    }
    // check if any any places have an insufficient number of tokens
    if (consumable.exists { case (_, count, tokens) ⇒ tokens.multisetSize < count })
      Seq.empty
    else {
      val consume = consumable.map {
        case (place, count, tokens) ⇒ place -> MultiSet.copyOff[Any](tokens.allElements.take(count))
      }.toMarking

      // TODO lazily compute all permutations instead of only providing the first result
      Seq(consume)
    }
  }

  def petriNet: RecipePetriNet =
    recipe.petriNet

  def transitions: Set[Transition] =
    recipe.petriNet.transitions

  def enabledTransitions(ofMarking: Marking[Place]): Set[Transition] =
    transitions
      .filter(consumableMarkings(_, ofMarking).nonEmpty)

  def transitionByLabel(label: String): Option[Transition] =
    transitions.find(_.label == label)

  def transitionById(transitionId: Long): Transition =
    transitions.getById(transitionId, "transition in petrinet")

  def isBlocked(transition: Transition): Boolean =
    executions.values
      .exists(t => t.transition.id == transition.id && t.hasFailed)

  def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] =
    enabledTransitions(ofMarking)
      .map(transition ⇒ transition -> consumableMarkings(transition, ofMarking)).toMap

  /** Checks if a transition can be fired automatically by the runtime (not triggered by some outside input).
    * By default, cold transitions (without in adjacent places) are not fired automatically.
    */
  def canBeFiredAutomatically(transition: Transition): Boolean =
    petriNet.incomingPlaces(transition).nonEmpty

  /** Finds the first transition that is enabled and can be fired automatically. */
  def firstEnabledExecution: Option[TransitionExecution] = {
    val enabled = enabledParameters(availableMarkings)
    val canFire = enabled.find { case (transition, _) ⇒
      !isBlocked(transition) && canBeFiredAutomatically(transition)
    }
    canFire.map { case (transition, markings) ⇒
      TransitionExecution(
        recipeInstanceId = recipeInstanceId,
        recipe = recipe,
        transition = transition,
        consume = markings.head,
        input = None,
        ingredients = ingredients,
        correlationId = None
      )
    }
  }

  /** Finds all enabled transitions that can be fired automatically. */
  def allEnabledExecutions: Set[TransitionExecution] = {
    val enabled  = enabledParameters(availableMarkings)
    val canFire = enabled.filter { case (transition, _) ⇒
      !isBlocked(transition) && canBeFiredAutomatically(transition)
    }
    canFire.map {
      case (transition, markings) =>
        TransitionExecution(
          recipeInstanceId = recipeInstanceId,
          recipe = recipe,
          transition = transition,
          consume = markings.head,
          input = None,
          ingredients = ingredients,
          correlationId = None
        )
    }.toSet
  }

  def recordCompletedExecutionOutcome(completedOutcome: TransitionExecution.Outcome.Completed): (RecipeInstanceState, Set[TransitionExecution]) = {
    val aggregated = aggregateOutputEvent(completedOutcome)
      .increaseSequenceNumber
      .aggregatePetriNetChanges(completedOutcome)
      .addReceivedCorrelationId(completedOutcome)
      .removeExecution(completedOutcome)
    val enabledExecutions = aggregated.allEnabledExecutions
    (aggregated.addExecution(enabledExecutions.toSeq: _*), enabledExecutions)
  }

  def addExecution(execution: TransitionExecution*): RecipeInstanceState =
    copy(executions = executions ++ execution.map(ex => ex.id -> ex))

  def removeExecution(outcome: TransitionExecution.Outcome.Completed): RecipeInstanceState =
    copy(executions = executions - outcome.transitionExecutionId)

  def aggregateOutputEvent(outcome: TransitionExecution.Outcome.Completed): RecipeInstanceState = {
    outcome.output match {
      case None => this
      case Some(outputEvent) =>
        copy(
          ingredients = ingredients ++ outputEvent.providedIngredients,
          events = events :+ EventMoment(outputEvent.name, System.currentTimeMillis()))
    }
  }

  def increaseSequenceNumber: RecipeInstanceState =
    copy(sequenceNumber = sequenceNumber + 1)

  def aggregatePetriNetChanges(outcome: TransitionExecution.Outcome.Completed): RecipeInstanceState = {
    val consumed: Marking[Place] = unmarshallMarking(petriNet.places, outcome.consumed)
    val produced: Marking[Place] = unmarshallMarking(petriNet.places, outcome.produced)
    copy(marking = (marking |-| consumed) |+| produced)
  }

  def addReceivedCorrelationId(outcome: TransitionExecution.Outcome.Completed): RecipeInstanceState =
    copy(receivedCorrelationIds = receivedCorrelationIds ++ outcome.correlationId)

  def transitionExecutionToFailedState(failedOutcome: TransitionExecution.Outcome.Failed): RecipeInstanceState = {
    val transition = transitionById(failedOutcome.transitionId)
    val consumed: Marking[Place] = unmarshallMarking(petriNet.places, failedOutcome.consume)
    lazy val newExecutionState =
      TransitionExecution(
        id = failedOutcome.transitionExecutionId,
        recipeInstanceId = recipeInstanceId,
        recipe = recipe,
        transition = transition,
        consume = consumed,
        input = failedOutcome.input,
        ingredients = ingredients,
        correlationId = failedOutcome.correlationId)
    val originalExecution = executions.getOrElse(failedOutcome.transitionExecutionId, newExecutionState)
    val updatedExecution = originalExecution.copy(state =
      TransitionExecution.State.Failed(failedOutcome.timeFailed, originalExecution.failureCount + 1, failedOutcome.failureReason, failedOutcome.exceptionStrategy))
    addExecution(updatedExecution)
  }
}

object RecipeInstanceState {

  def empty(recipeInstanceId: String, recipe: CompiledRecipe, createdOn: Long): RecipeInstanceState =
    RecipeInstanceState(
      recipeInstanceId,
      recipe,
      createdOn,
      sequenceNumber = 0,
      marking = recipe.initialMarking,
      ingredients = Map.empty,
      events = List.empty,
      receivedCorrelationIds = Set.empty,
      executions = Map.empty
    )
}

