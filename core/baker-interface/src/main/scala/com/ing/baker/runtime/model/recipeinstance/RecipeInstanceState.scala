package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api.{Marking, MultiSet}
import com.ing.baker.runtime.scaladsl.EventMoment
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api._
import com.ing.baker.types.Value

import scala.collection.immutable

case class RecipeInstanceState(
                                recipeInstanceId: String,
                                recipe: CompiledRecipe,
                                createdOn: Long,
                                sequenceNumber: Long,
                                marking: Marking[Place],
                                ingredients: Map[String, Value],
                                events: List[EventMoment],
                                completedCorrelationIds: Set[String],
                                executions: Map[Long, TransitionExecution],
                                retryingExecutions: Set[Long]
                              ) extends RecipeInstanceEventValidation {

  def isInactive: Boolean =
    executions.values.forall(_.isInactive)

  def getInteractionExecution(interactionName: String): Option[TransitionExecution] =
    for {
      transition <- recipe.interactionTransitions.find(_.interactionName == interactionName)
      transitionExecution <- executions.collectFirst {
        case (_, execution) if execution.transition.id == transition.id => execution }
    } yield transitionExecution

  def sensoryEventByName(name: String): Option[EventDescriptor] =
    recipe.sensoryEvents.find(_.name == name)

  def allMarking: Marking[Place] =
    marking

  /** The marking that is already used by running jobs */
  private def reservedMarkings: Marking[Place] =
    executions
      .map { case (_, execution) ⇒ execution.consume }
      .reduceOption(_ |+| _)
      .getOrElse(Marking.empty)

  /** Markings that are available for an execution. */
  def availableMarkings: Marking[Place] =
    allMarking |-| reservedMarkings

  def consumableTokens(p: Place, transition: Transition, ofMarking: Marking[Place]): MultiSet[Any] = {
    val edge = petriNet.findPTEdge(p, transition).map(_.asInstanceOf[Edge]).get
    ofMarking.get(p) match {
      case None ⇒ MultiSet.empty
      case Some(tokens) ⇒ tokens.filter { case (e, _) ⇒ edge.isAllowed(e) }
    }
  }

  def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {
    // TODO this is not the most efficient, should break early when consumable tokens < edge weight
    val consumable = recipe.petriNet.inMarking(t).map {
      case (place, count) ⇒ (place, count, consumableTokens(place, t, ofMarking))
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
      .exists(t => t.transition.id == transition.id && t.isBlocked)

  def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] =
    enabledTransitions(ofMarking)
      .map(transition ⇒ transition -> consumableMarkings(transition, ofMarking)).toMap

  /** Checks if a transition can be fired automatically by the runtime (not triggered by some outside input).
    * By default, cold transitions (without in adjacent places) are not fired automatically.
    */
  def canBeFiredAutomatically(transition: Transition): Boolean =
    transition match {
      case EventTransition(_, true, _) => false
      case _ => true
    }

  def addRetryingExecution(transitionExecutionId: Long): RecipeInstanceState =
    copy(retryingExecutions = retryingExecutions + transitionExecutionId)

  def removeRetryingExecution(transitionExecutionId: Long): RecipeInstanceState =
    copy(retryingExecutions = retryingExecutions - transitionExecutionId)

  /** Finds all enabled transitions that can be fired automatically. */
  def allEnabledExecutions: (RecipeInstanceState, Set[TransitionExecution]) = {
    val enabled  = enabledParameters(availableMarkings)
    val canFire = enabled.filter { case (transition, _) ⇒
      !isBlocked(transition) && canBeFiredAutomatically(transition)
    }
    val executions = canFire.map {
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
    }.toSeq
    addExecution(executions: _*) -> executions.toSet
  }

  def recordCompletedExecutionOutcome(transitionExecution: TransitionExecution, completedOutcome: TransitionExecution.Outcome.Completed): (RecipeInstanceState, Set[TransitionExecution]) = {
    aggregateOutputEvent(completedOutcome)
      .increaseSequenceNumber
      .aggregatePetriNetChanges(transitionExecution, completedOutcome)
      .addCompletedCorrelationId(transitionExecution)
      .removeExecution(transitionExecution)
      .allEnabledExecutions
  }

  def addExecution(execution: TransitionExecution*): RecipeInstanceState =
    copy(executions = executions ++ execution.map(ex => ex.id -> ex))

  def removeExecution(transitionExecution: TransitionExecution): RecipeInstanceState =
    copy(executions = executions - transitionExecution.id)

  def aggregateOutputEvent(outcome: TransitionExecution.Outcome.Completed): RecipeInstanceState =
    outcome.output match {
      case None => this
      case Some(outputEvent) =>
        copy(
          ingredients = ingredients ++ outputEvent.providedIngredients,
          events = events :+ EventMoment(outputEvent.name, System.currentTimeMillis()))
    }

  def increaseSequenceNumber: RecipeInstanceState =
    copy(sequenceNumber = sequenceNumber + 1)

  def aggregatePetriNetChanges(transitionExecution: TransitionExecution, outcome: TransitionExecution.Outcome.Completed): RecipeInstanceState =
    copy(marking = (marking |-| transitionExecution.consume) |+| transitionExecution.producedMarking(outcome.output))

  def addCompletedCorrelationId(transitionExecution: TransitionExecution): RecipeInstanceState =
    copy(completedCorrelationIds = completedCorrelationIds ++ transitionExecution.correlationId)

  def transitionExecutionToFailedState(transitionExecution: TransitionExecution, failedOutcome: TransitionExecution.Outcome.Failed): RecipeInstanceState =
    addExecution(transitionExecution.toFailedState(failedOutcome))
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
      completedCorrelationIds = Set.empty,
      executions = Map.empty,
      retryingExecutions = Set.empty
    )
}

