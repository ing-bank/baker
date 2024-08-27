package com.ing.baker.runtime.akka.actor.process_instance.internal

import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api._

import scala.util.Random

object Instance {
  def uninitialized[S](process: PetriNet): Instance[S] = Instance[S](process, 0, Marking.empty, Map.empty, null.asInstanceOf[S], Map.empty, Set.empty)
}

/**
 * Keeps the state of a petri net instance.
 */
case class Instance[S](
    petriNet: PetriNet,
    sequenceNr: Long,
    marking: Marking[Place],
    delayedTransitionIds: Map[Id, Int],
    state: S,
    jobs: Map[Long, Job[S]],
    receivedCorrelationIds: Set[String]) {

  /**
   * The marking that is already used by running jobs
   */
  lazy val reservedMarking: Marking[Place] = jobs.map {
    case (id, job) => job.consume }
    .reduceOption(_ |+| _)
    .getOrElse(Marking.empty)

  /**
   * The marking that is available for new jobs
   */
  lazy val availableMarking: Marking[Place] = marking |-| reservedMarking

  /**
    * The active jobs for the process instance.
    */
  def activeJobs: Iterable[Job[S]] = jobs.values.filter(_.isActive)

  /**
    * Checks whether a transition is blocked by a previous failure.
    */
  def isBlocked(transition: Transition): Boolean = jobs.values.collectFirst {
    case Job(_, _, _, `transition`, _, _, Some(ExceptionState(_, _, reason, _))) =>
      s"Transition '$transition' is blocked because it failed previously with: $reason"
  }.isDefined

  def hasReceivedCorrelationId(correlationId: String): Boolean =
    receivedCorrelationIds.contains(correlationId) || jobs.values.exists(_.correlationId.contains(correlationId))

  def nextJobId(): Long = Random.nextLong()
}
