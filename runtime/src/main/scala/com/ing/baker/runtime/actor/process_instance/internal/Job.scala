package com.ing.baker.runtime.actor.process_instance.internal

import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.actor.process_instance.internal.ExceptionStrategy.RetryWithDelay

/**
 * A Job encapsulates all the parameters that make a firing transition in a petri net.
 */
case class Job[P, T, S](
    id: Long,
    correlationId: Option[String],
    processState: S,
    transition: T,
    consume: Marking[P],
    input: Any,
    failure: Option[ExceptionState] = None) {

  def isActive: Boolean = failure match {
    case Some(ExceptionState(_, _, _, RetryWithDelay(_))) ⇒ true
    case None                                             ⇒ true
    case _                                                ⇒ false
  }

  def failureCount: Int = failure.map(_.failureCount).getOrElse(0)
}
