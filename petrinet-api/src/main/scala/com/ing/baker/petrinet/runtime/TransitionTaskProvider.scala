package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api.PetriNet

/**
 * Provides a task for a transition.
 *
 * @tparam State The state type of the net.
 * @tparam P The place type of the net.
 * @tparam T The transition type of the net.
 */
trait TransitionTaskProvider[P[_], T[_], State, E] {

  /**
   * Given a transition returns an TransitionTask
   *
   * @tparam Input  The input type of the transition.
   * @param t       The transition.
   * @return
   */
  def apply[Input](petriNet: PetriNet[P[_], T[_]], t: T[Input]): TransitionTask[P, Input, State, E]
}