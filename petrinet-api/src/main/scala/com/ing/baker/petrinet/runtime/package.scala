package com.ing.baker.petrinet

import cats.effect.IO
import com.ing.baker.petrinet.api.Marking

package object runtime {

  /**
   * An (asynchronous) function associated with a transition
   *
   * @tparam Output The output emitted by the transition.
   * @tparam State  The state the transition closes over.
   */
  type TransitionTask[P, State, E] = (Marking[P], State, Any) ⇒ IO[(Marking[P], E)]

  /**
   * An event sourcing function associated with a transition
   *
   * @tparam S The state type
   * @tparam E The event type
   */
  type EventSource[S, E] = S ⇒ E ⇒ S

  implicit class IOHandleErrors[T](io: IO[T]) {

    def handle[Y >: T](pf: PartialFunction[Throwable, Y]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).map(IO.pure(_)).getOrElse(IO.raiseError(throwable))
      }

    def handleWith[Y >: T](pf: PartialFunction[Throwable, IO[Y]]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).getOrElse(IO.raiseError(throwable))
      }
  }
}
