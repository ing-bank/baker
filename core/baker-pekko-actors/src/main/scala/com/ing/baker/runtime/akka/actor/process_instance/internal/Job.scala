package com.ing.baker.runtime.akka.actor.process_instance.internal

import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.akka.actor.process_instance.internal.ExceptionStrategy.RetryWithDelay

/**
 * A Job encapsulates all the parameters that make a firing transition in a petri net.
 */
case class Job[S](
                   id: Long,
                   correlationId: Option[String],
                   processState: S,
                   transition: Transition,
                   consume: Marking[Place],
                   input: Any,
                   failure: Option[ExceptionState] = None) {

  def isActive: Boolean = failure match {
    case Some(ExceptionState(_, _, _, RetryWithDelay(_))) => true
    case None                                             => true
    case _                                                => false
  }

  def failureCount: Int = failure.map(_.failureCount).getOrElse(0)
}
