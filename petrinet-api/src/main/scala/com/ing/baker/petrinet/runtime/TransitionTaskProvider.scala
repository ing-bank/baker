package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api.PetriNet

/**
 * Provides a task for a transition.
 *
 * @tparam State The state type of the net.
 * @tparam P The place type of the net.
 * @tparam T The transition type of the net.
 */
trait TransitionTaskProvider[P, T, State, E] {

  /**
   * Given a transition returns an TransitionTask
   *
   * @param t       The transition.
   * @return
   */
  def apply(petriNet: PetriNet[P, T], t: T): TransitionTask[P, State, E]
}