package com.ing.baker.runtime.model

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.{Place, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api.{Marking, MultiSet}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.types.Value
import com.ing.baker.petrinet.api._

import scala.util.Random

case class RecipeInstanceState(recipeInstanceId: String,
                               recipe: CompiledRecipe,
                               //sequenceNr: Long,
                               marking: Marking[Place],
                               ingredients: Map[String, Value],
                               events: List[(Int, EventInstance)],
                               firings: Map[Long, TransitionFiring]
                               //receivedCorrelationIds: Set[String]
                              ) {

  lazy val petriNet: RecipePetriNet = recipe.petriNet

  def reservedMarking: Marking[Place] =
    firings.map { case (_, firing) ⇒ firing.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

  def availableMarking: Marking[Place] =
    marking |-| reservedMarking

  def activeFirings: List[TransitionFiring] =
    firings.values.filter(_.isActive).toList

  def isBlocked(transition: Transition): Boolean =
    firings.values.exists(t => t.transition == transition && t.isFailed)

  def createFiring(transition: Transition, input: EventInstance): Either[String, (RecipeInstanceState, TransitionFiring)] = {
    enabledParameters(availableMarking).get(transition) match {
      case None ⇒
        Left(s"Not enough consumable tokens. This might have been caused because the event has already been fired up the the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired")
      case Some(params) ⇒
        val firingId = Random.nextLong()
        val firing = TransitionFiring(firingId, transition, params.head, input)
        val updatedInstance = copy(firings = firings + (firing.id -> firing))
        Right(updatedInstance -> firing)
    }
  }

  def isEnabled(t: Transition, ofMarking: Marking[Place]): Boolean =
    consumableMarkings(t, ofMarking).nonEmpty

  def enabledTransitions(ofMarking: Marking[Place]): Iterable[Transition] =
    petriNet.transitions.filter(t => isEnabled(t, ofMarking))

  def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] =
    enabledTransitions(ofMarking).view.map(t ⇒ t -> consumableMarkings(t, ofMarking)).toMap

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

object RecipeInstanceState {

  def empty(recipe: CompiledRecipe, recipeInstanceId: String): RecipeInstanceState =
    RecipeInstanceState(
      recipe = recipe,
      marking = recipe.initialMarking,
      recipeInstanceId = recipeInstanceId,
      ingredients = Map.empty,
      events = List.empty,
      firings = Map.empty
    )
}

