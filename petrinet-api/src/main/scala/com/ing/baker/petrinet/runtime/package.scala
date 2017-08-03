package com.ing.baker.petrinet

import com.ing.baker.petrinet.api.Marking
import fs2.Task

package object runtime {

  /**
   * An exception handler function associated with a transition.
   */
  type TransitionExceptionHandler = (Throwable, Int) ⇒ ExceptionStrategy

  /**
   * An (asynchronous) function associated with a transition
   *
   * @tparam Input  The input delivered to the transition from outside the process.
   * @tparam Output The output emitted by the transition.
   * @tparam State  The state the transition closes over.
   */
  type TransitionTask[P[_], Input, Output, State] = (Marking[P], State, Input) ⇒ Task[(Marking[P], Output)]

  /**
   * An event sourcing function associated with a transition
   *
   * @tparam S The state type
   * @tparam E The event type
   */
  type EventSource[S, E] = S ⇒ E ⇒ S
}
