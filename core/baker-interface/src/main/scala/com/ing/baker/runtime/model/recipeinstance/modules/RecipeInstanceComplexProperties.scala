package com.ing.baker.runtime.model.recipeinstance.modules

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.petrinet.{Place, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api.{Marking, MultiSet, _}
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, TransitionExecution}

trait RecipeInstanceComplexProperties { recipeInstance: RecipeInstance =>

  def activeExecutions: Iterable[TransitionExecution] =
    recipeInstance.executions.values.filter(_.isActive)

  def sensoryEventByName(name: String): Option[EventDescriptor] =
    recipeInstance.recipe.sensoryEvents.find(_.name == name)

  def allMarking: Marking[Place] =
    recipeInstance.marking

  /** The marking that is already used by running jobs */
  def reservedMarkings: Marking[Place] =
    recipeInstance.executions
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
    val consumable = recipeInstance.recipe.petriNet.inMarking(t).map {
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
    recipeInstance.recipe.petriNet

  def transitions: Set[Transition] =
    recipeInstance.recipe.petriNet.transitions

  def enabledTransitions(ofMarking: Marking[Place]): Set[Transition] =
    transitions
      .filter(consumableMarkings(_, ofMarking).nonEmpty)

  def transitionByLabel(label: String): Option[Transition] =
    transitions.find(_.label == label)

  def transitionById(transitionId: Long): Transition =
    transitions.getById(transitionId, "transition in petrinet")

  def isBlocked(transition: Transition): Boolean =
    recipeInstance.executions.values
      .exists(t => t.transition.id == transition.id && t.isFailed)

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
        recipeInstanceId = recipeInstance.recipeInstanceId,
        recipe = recipeInstance.recipe,
        transition = transition,
        consume = markings.head,
        input = None,
        ingredients = recipeInstance.ingredients,
        correlationId = None
      )
    }
  }

  /** Finds all enabled transitions that can be fired automatically. */
  def allEnabledExecutions: Seq[TransitionExecution] = {
    val enabled  = enabledParameters(availableMarkings)
    val canFire = enabled.filter { case (transition, _) ⇒
      !isBlocked(transition) && canBeFiredAutomatically(transition)
    }
    canFire.map {
      case (transition, markings) =>
        TransitionExecution(
          recipeInstanceId = recipeInstance.recipeInstanceId,
          recipe = recipeInstance.recipe,
          transition = transition,
          consume = markings.head,
          input = None,
          ingredients = recipeInstance.ingredients,
          correlationId = None
        )
    }.toSeq
  }
}
