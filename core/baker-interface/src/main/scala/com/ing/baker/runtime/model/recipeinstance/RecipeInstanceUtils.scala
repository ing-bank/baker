package com.ing.baker.runtime.model.recipeinstance

import cats.effect.{Clock, Sync}
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.scaladsl.EventInstance
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.{Logger, LoggerFactory}

/** Utility functions of the RecipeInstance to help validate the input events (to create firings)
  * and to extract information about the petri net (like checking for blocked transitions or enabled parameters)
  *
  */
private[recipeinstance] trait RecipeInstanceUtils extends LazyLogging { self: RecipeInstance =>

  val log: Logger = LoggerFactory.getLogger("com.ing.baker.runtime.model.recipeinstance.RecipeInstance")

  /** Firing Validation ********************************************************************************************* */

  type Reason = String

  type FireTransitionValidation[+A] =
    Either[(FireSensoryEventRejection, Reason), A]

  protected def validateInputAndCreateExecution[F[_]](
    transitionId: Long,
    input: EventInstance,
    correlationId: Option[String]
  )(implicit
    effect: Sync[F],
    clock: Clock[F]
  ): FireTransitionValidation[TransitionExecution] = {
    val transition = petriNetTransition(transitionId)
    for {
      _ <- validateReceivedCorrelationId(correlationId)
      _ <- validateIsBlocked(transition)
      params <- validateConsumableTokens(transition)
    } yield TransitionExecution(
      recipeInstanceId = recipeInstanceId,
      recipe = recipe,
      transition = transition,
      consume = params.head,
      input = Some(input),
      ingredients = ingredients,
      correlationId = correlationId
    )
  }

  /*
  def activeFirings: List[TransitionFiring[F]] =
    firings.values.filter(_.isActive).toList
   */

  private def reject[A](rejection: FireSensoryEventRejection, explanation: String): FireTransitionValidation[A] =
    Left(rejection -> explanation)

  private def accept[A](a: A): FireTransitionValidation[A] =
    Right(a)

  private def continue: FireTransitionValidation[Unit] =
    accept(())

  private def validateReceivedCorrelationId(correlationId: Option[String]): FireTransitionValidation[Unit] =
    correlationId match {
      case Some(correlationId) if receivedCorrelationIds.contains(correlationId) || executions.values.exists(_.correlationId.contains(correlationId)) =>
        reject(FireSensoryEventRejection.AlreadyReceived(recipeInstanceId, correlationId), s"The correlation id $correlationId was previously received by another fire transition command")
      case _ => continue
    }

  private def validateIsBlocked(transition: Transition): FireTransitionValidation[Unit] =
    if (isBlocked(transition)) reject(FireSensoryEventRejection.FiringLimitMet(recipeInstanceId), "Transition is blocked by a previous failure")
    else continue

  private def validateConsumableTokens(transition: Transition): FireTransitionValidation[Iterable[Marking[Place]]] =
    enabledParameters(availableMarking).get(transition) match {
      case None ⇒
        reject(FireSensoryEventRejection.FiringLimitMet(recipeInstanceId), s"Not enough consumable tokens. This might have been caused because the event has already been fired up to the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired")
      case Some(params) ⇒
        accept(params)
    }

  /** State management ********************************************************************************************** */

  protected def addExecution(execution: TransitionExecution*): RecipeInstance =
    self.copy(executions = self.executions ++ execution.map(e => e.id -> e).toMap)

  /** Petri Net management ****************************************************************************************** */

  /** The marking that is already used by running jobs */
  private def reservedMarking: Marking[Place] =
    executions.map { case (_, execution) ⇒ execution.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

  /** Markings that are available for an execution. */
  private def availableMarking: Marking[Place] =
    marking |-| reservedMarking

  private def petriNetTransition(transitionId: Long): Transition =
    recipe.petriNet.transitions.getById(transitionId, "transition in petrinet")

  private def isBlocked(transition: Transition): Boolean =
    executions.values.exists(t => t.transition.id == transition.id && t.isFailed)

  private def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] = {

    def enabledTransitions(ofMarking: Marking[Place]): Set[Transition] =
      recipe.petriNet.transitions.filter(t => consumableMarkings(t, ofMarking).nonEmpty)

    enabledTransitions(ofMarking).map(t ⇒ t -> consumableMarkings(t, ofMarking)).toMap
  }

  private def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {
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

  private def consumableTokens(p: Place, ofMarking: Marking[Place]): MultiSet[Any] =
    ofMarking.getOrElse(p, MultiSet.empty)

  /** Checks if a transition can be fired automatically by the runtime (not triggered by some outside input).
    * By default, cold transitions (without in adjacent places) are not fired automatically.
    */
  def canBeFiredAutomatically(transition: Transition): Boolean =
    recipe.petriNet.incomingPlaces(transition).nonEmpty

  /** Finds the first transition that is enabled and can be fired automatically. */
  def firstEnabledExecution: Option[TransitionExecution] =
    enabledParameters(availableMarking).find {
      case (transition, _) ⇒ !isBlocked(transition) && canBeFiredAutomatically(transition)
    }.map {
      case (transition, markings) ⇒
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

  /** Finds all enabled transitions that can be fired automatically. */
  def allEnabledExecutions: Seq[TransitionExecution] =
    enabledParameters(availableMarking).filter {
      case (transition, _) ⇒ !isBlocked(transition) && canBeFiredAutomatically(transition)
    }.map {
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
}
