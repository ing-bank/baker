package com.ing.baker.petrinet.runtime

import cats.data.State
import com.ing.baker.petrinet.api._

/**
 * Interface for deciding which (transition, marking) parameters are 'enabled' or 'fireable' in a petri net.
 *
 * @tparam P Place
 * @tparam T Transition
 */
trait TokenGame[P[_], T] {

  def enabledParameters(petriNet: PetriNet[P[_], T])(m: Marking[P]): Map[T, Iterable[Marking[P]]] =
    enabledTransitions(petriNet)(m).view.map(t ⇒ t -> consumableMarkings(petriNet)(m, t)).toMap

  def consumableMarkings(petriNet: PetriNet[P[_], T])(marking: Marking[P], t: T): Iterable[Marking[P]] = {
    // TODO this is not the most efficient, should break early when consumable tokens < edge weight
    val consumable = petriNet.inMarking(t).map {
      case (place, count) ⇒ (place, count, consumableTokens(petriNet)(marking, place, t))
    }

    // check if any
    if (consumable.exists { case (place, count, tokens) ⇒ tokens.multisetSize < count })
      Seq.empty
    else {
      val consume = consumable.map {
        case (place, count, tokens) ⇒ place -> MultiSet.copyOff(tokens.allElements.take(count))
      }.toMarking

      // TODO lazily compute all permutations instead of only providing the first result
      Seq(consume)
    }
  }

  def consumableTokens(petriNet: PetriNet[P[_], T])(marking: Marking[P], p: P[_], t: T): MultiSet[_] =
    marking.getOrElse(p.asInstanceOf[P[Any]], MultiSet.empty)

  /**
   * Checks whether a transition is 'enabled' in a marking.
   *
   * @param marking The marking.
   * @param t The transition.
   * @return
   */
  def isEnabled(petriNet: PetriNet[P[_], T])(marking: Marking[P], t: T): Boolean = consumableMarkings(petriNet)(marking, t).nonEmpty

  /**
   * Returns all enabled transitions for a marking.
   *
   * @param marking marking
   * @return
   */
  def enabledTransitions(petriNet: PetriNet[P[_], T])(marking: Marking[P]): Iterable[T] =
    petriNet.transitions.filter(t ⇒ consumableMarkings(petriNet)(marking, t).nonEmpty)

  /**
    * Fires a specific transition with input, computes the marking it should consume
    */
  def createJob[S, I](transition: T, input: I, correlationId: Option[String] = None): State[Instance[P, T, S], Either[String, Job[P, T, S]]] =
    State { instance ⇒
      instance.isBlockedReason(transition) match {
        case Some(reason) ⇒
          (instance, Left(reason))
        case None ⇒
          enabledParameters(instance.process)(instance.availableMarking).get(transition) match {
            case None ⇒
              (instance, Left(s"Not enough consumable tokens"))
            case Some(params) ⇒
              val job = Job[P, T, S](instance.nextJobId(), correlationId, instance.state, transition, params.head, input)
              val updatedInstance = instance.copy[P, T, S](jobs = instance.jobs + (job.id -> job))
              (updatedInstance, Right(job))
          }
      }
    }

  /**
    * Checks if a transition is automatically fireable by the runtime (not triggered by some outside input)
    *
    * By default, cold transitions (without in adjacent places) are not picked.
    */
  def isAutoFireable[S](instance: Instance[P, T, S], t: T) = !instance.process.incomingPlaces(t).isEmpty

  /**
    * Finds the (optional) first transition that is enabled & automatically fireable
    */
  def firstEnabledJob[S]: State[Instance[P, T, S], Option[Job[P, T, S]]] = State { instance ⇒
    enabledParameters(instance.process)(instance.availableMarking).find {
      case (t, markings) ⇒ !instance.isBlockedReason(t).isDefined && isAutoFireable(instance, t)
    }.map {
      case (t, markings) ⇒
        val job = Job[P, T, S](instance.nextJobId(), None, instance.state, t, markings.head, null)
        (instance.copy[P, T, S](jobs = instance.jobs + (job.id -> job)), Some(job))
    }.getOrElse((instance, None))
  }

  /**
    * Finds all automated enabled transitions.
    */
  def allEnabledJobs[S]: State[Instance[P, T, S], Set[Job[P, T, S]]] =
    firstEnabledJob[S].flatMap {
      case None      ⇒ State.pure(Set.empty)
      case Some(job) ⇒ allEnabledJobs[S].map(_ + job)
    }
}
