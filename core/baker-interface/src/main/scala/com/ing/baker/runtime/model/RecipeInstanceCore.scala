package com.ing.baker.runtime.model

import cats.Monad
import cats.data.EitherT
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.{Place, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api.{Marking, MultiSet}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.types.Value
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection

import scala.util.Random
import cats.implicits._

case class RecipeInstanceCore[F[_]](
    recipeInstanceId: String,
    recipe: CompiledRecipe,
    //sequenceNr: Long,
    marking: Marking[Place],
    ingredients: Map[String, Value],
    events: List[(Int, EventInstance)],
    firings: Map[Long, TransitionFiring],
    receivedCorrelationIds: Set[String]
  )(implicit eff: Monad[F]) {

  lazy val petriNet: RecipePetriNet = recipe.petriNet

  type FireTransitionValidation[A] = EitherT[F, (FireSensoryEventRejection, String), A]

  def reject[A](rejection: FireSensoryEventRejection, explanation: String): FireTransitionValidation[A] =
    EitherT.leftT(rejection -> explanation)

  def accept[A](a: A): FireTransitionValidation[A] =
    EitherT.rightT(a)

  def continue: FireTransitionValidation[Unit] =
    accept(())

  def fireTransition(transitionId: Long, input: EventInstance, correlationId: Option[String] = None): FireTransitionValidation[(RecipeInstanceCore[F], F[Unit])] = {

    val transition = petriNet.transitions.getById(transitionId, "transition in petrinet")

    def validateReceivedCorrelationId: FireTransitionValidation[Unit] =
      correlationId match {
        case Some(correlationId) if receivedCorrelationIds.contains(correlationId) || firings.values.exists(_.correlationId.contains(correlationId)) =>
          reject(FireSensoryEventRejection.AlreadyReceived(recipeInstanceId, correlationId), s"The correlation id $correlationId was previously received by another fire transition command")
        case _ => continue
      }

    def validateIsBlocked: FireTransitionValidation[Unit] =
      if (isBlocked(transition)) reject(FireSensoryEventRejection.FiringLimitMet(recipeInstanceId), "Transition is blocked by a previous failure")
      else continue

    def validateConsumableTokens: FireTransitionValidation[Iterable[Marking[Place]]] =
      enabledParameters(availableMarking).get(transition) match {
        case None ⇒
          reject(FireSensoryEventRejection.FiringLimitMet(recipeInstanceId), s"Not enough consumable tokens. This might have been caused because the event has already been fired up to the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired")
        case Some(params) ⇒
          accept(params)
      }

    for {
      _ <- validateReceivedCorrelationId
      _ <- validateIsBlocked
      params <- validateConsumableTokens
      firing = TransitionFiring(Random.nextLong(), correlationId, transition, params.head, input)
      updatedInstance = copy(firings = firings + (firing.id -> firing))
      //executeJob(job, sender()) // TODO HERE IS THE NEXT STEP, FIND IT ON
    } yield updatedInstance -> eff.unit
  }


  def reservedMarking: Marking[Place] =
    firings.map { case (_, firing) ⇒ firing.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

  def availableMarking: Marking[Place] =
    marking |-| reservedMarking

  def activeFirings: List[TransitionFiring] =
    firings.values.filter(_.isActive).toList

  def isBlocked(transition: Transition): Boolean =
    firings.values.exists(t => t.transition == transition && t.isFailed)

  def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] = {

    def enabledTransitions(ofMarking: Marking[Place]): Set[Transition] =
      petriNet.transitions.filter(t => consumableMarkings(t, ofMarking).nonEmpty)

    enabledTransitions(ofMarking).map(t ⇒ t -> consumableMarkings(t, ofMarking)).toMap
  }

  def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {
    // TODO this is not the most efficient, should break early when consumable tokens < edge weight
    val consumable = petriNet.inMarking(t).map {
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

  def consumableTokens(p: Place, ofMarking: Marking[Place]): MultiSet[Any] = ofMarking.getOrElse(p, MultiSet.empty)
}

object RecipeInstanceCore {

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String): RecipeInstanceCore[F] =
    RecipeInstanceCore(
      recipe = recipe,
      marking = recipe.initialMarking,
      recipeInstanceId = recipeInstanceId,
      ingredients = Map.empty,
      events = List.empty,
      firings = Map.empty,
      receivedCorrelationIds = Set.empty
    )
}
