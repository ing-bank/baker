package com.ing.baker.runtime.model.recipeinstance

import cats.effect.{Clock, Sync}
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.scaladsl.EventInstance

import scala.util.Random

private[recipeinstance] class TransitionFiringValidation[F[_]](
                                                                recipeInstance: RecipeInstance[F],
                                                                transitionId: Long,
                                                                input: EventInstance,
                                                                correlationId: Option[String]
                                                              )(implicit effect: Sync[F], clock: Clock[F]) {

  type Reason = String

  type FireTransitionValidation[+A] =
    Either[(FireSensoryEventRejection, Reason), A]

  def validate: FireTransitionValidation[TransitionFiring[F]] = {
    for {
      _ <- validateReceivedCorrelationId
      _ <- validateIsBlocked
      params <- validateConsumableTokens
    } yield TransitionFiring[F](
      id = Random.nextLong(),
      recipeInstanceId = recipeInstance.recipeInstanceId,
      recipe = recipeInstance.recipe,
      transition = transition,
      consume = params.head,
      input = input,
      ingredients = recipeInstance.ingredients,
      correlationId = correlationId,
      interactionManager = recipeInstance.interactionManager,
      eventStream = recipeInstance.eventStream
    )
  }

  private def reject[A](rejection: FireSensoryEventRejection, explanation: String): FireTransitionValidation[A] =
    Left(rejection -> explanation)

  private def accept[A](a: A): FireTransitionValidation[A] =
    Right(a)

  private def continue: FireTransitionValidation[Unit] =
    accept(())

  private def transition =
    recipeInstance.recipe.petriNet.transitions.getById(transitionId, "transition in petrinet")

  private def validateReceivedCorrelationId: FireTransitionValidation[Unit] =
    correlationId match {
      case Some(correlationId) if recipeInstance.receivedCorrelationIds.contains(correlationId) || recipeInstance.firings.values.exists(_.correlationId.contains(correlationId)) =>
        reject(FireSensoryEventRejection.AlreadyReceived(recipeInstance.recipeInstanceId, correlationId), s"The correlation id $correlationId was previously received by another fire transition command")
      case _ => continue
    }

  private def validateIsBlocked: FireTransitionValidation[Unit] =
    if (isBlocked(transition)) reject(FireSensoryEventRejection.FiringLimitMet(recipeInstance.recipeInstanceId), "Transition is blocked by a previous failure")
    else continue

  private def validateConsumableTokens: FireTransitionValidation[Iterable[Marking[Place]]] =
    enabledParameters(availableMarking).get(transition) match {
      case None ⇒
        reject(FireSensoryEventRejection.FiringLimitMet(recipeInstance.recipeInstanceId), s"Not enough consumable tokens. This might have been caused because the event has already been fired up to the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired")
      case Some(params) ⇒
        accept(params)
    }

  private def reservedMarking: Marking[Place] =
    recipeInstance.firings.map { case (_, firing) ⇒ firing.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

  private def availableMarking: Marking[Place] =
    recipeInstance.marking |-| reservedMarking

  /*
  def activeFirings: List[TransitionFiring[F]] =
    firings.values.filter(_.isActive).toList
   */

  private def isBlocked(transition: Transition): Boolean =
    recipeInstance.firings.values.exists(t => t.transition == transition && t.isFailed)

  private def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] = {

    def enabledTransitions(ofMarking: Marking[Place]): Set[Transition] =
      recipeInstance.recipe.petriNet.transitions.filter(t => consumableMarkings(t, ofMarking).nonEmpty)

    enabledTransitions(ofMarking).map(t ⇒ t -> consumableMarkings(t, ofMarking)).toMap
  }

  private def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {
    // TODO this is not the most efficient, should break early when consumable tokens < edge weight
    val consumable = recipeInstance.recipe.petriNet.inMarking(t).map {
      case (place, count) ⇒ (place, count, consumableTokens(place, ofMarking))
    }
    // check if any any places have an insufficient number of tokens
    if (consumable.exists {case (_, count, tokens) ⇒ tokens.multisetSize < count})
      Seq.empty
    else {
      val consume = consumable.map {
        case (place, count, tokens) ⇒ place -> MultiSet.copyOff[Any](tokens.allElements.take(count))
      }.toMarking

      // TODO lazily compute all permutations instead of only providing the first result
      Seq(consume)
    }
  }

  private def consumableTokens(p: Place, ofMarking: Marking[Place]): MultiSet[Any] = ofMarking.getOrElse(p, MultiSet.empty)
}
