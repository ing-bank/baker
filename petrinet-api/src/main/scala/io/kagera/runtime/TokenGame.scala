package io.kagera.runtime

import io.kagera.api._

/**
 * Interface for deciding which (transition, marking) parameters are 'enabled' or 'fireable' in a petri net.
 *
 * @tparam P Place
 * @tparam T Transition
 */
trait TokenGame[P[_], T[_, _]] {

  def enabledParameters(petriNet: PetriNet[P[_], T[_, _]])(m: Marking[P]): Map[T[_, _], Iterable[Marking[P]]] =
    enabledTransitions(petriNet)(m).view.map(t ⇒ t -> consumableMarkings(petriNet)(m, t)).toMap

  def consumableMarkings(petriNet: PetriNet[P[_], T[_, _]])(marking: Marking[P], t: T[_, _]): Iterable[Marking[P]] = {
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

  def consumableTokens(petriNet: PetriNet[P[_], T[_, _]])(marking: Marking[P], p: P[_], t: T[_, _]): MultiSet[_] =
    marking.getOrElse(p.asInstanceOf[P[Any]], MultiSet.empty)

  /**
   * Checks whether a transition is 'enabled' in a marking.
   *
   * @param marking The marking.
   * @param t The transition.
   * @return
   */
  def isEnabled(petriNet: PetriNet[P[_], T[_, _]])(marking: Marking[P], t: T[_, _]): Boolean = consumableMarkings(petriNet)(marking, t).nonEmpty

  /**
   * Returns all enabled transitions for a marking.
   *
   * @param marking marking
   * @return
   */
  def enabledTransitions(petriNet: PetriNet[P[_], T[_, _]])(marking: Marking[P]): Iterable[T[_, _]] =
    petriNet.transitions.filter(t ⇒ consumableMarkings(petriNet)(marking, t).nonEmpty)
}
