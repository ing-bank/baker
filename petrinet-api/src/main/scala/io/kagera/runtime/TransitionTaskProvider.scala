package io.kagera.runtime

import io.kagera.api.PetriNet

/**
 * Provides a task for a transition.
 *
 * @tparam State The state type of the net.
 * @tparam P The place type of the net.
 * @tparam T The transition type of the net.
 */
trait TransitionTaskProvider[State, P[_], T[_, _]] {

  /**
   * Given a transition returns an TransitionTask
   *
   * @tparam Input  The input type of the transition.
   * @tparam Output The output type of the transition.
   * @param t       The transition.
   * @return
   */
  def apply[Input, Output](petriNet: PetriNet[P[_], T[_, _]], t: T[Input, Output]): TransitionTask[P, Input, Output, State]
}