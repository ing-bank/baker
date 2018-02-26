package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api._

import scala.util.Random

object Instance {
  def uninitialized[P[_], T[_, _], S](process: PetriNet[P[_], T[_, _]]): Instance[P, T, S] = Instance[P, T, S](process, 0, Marking.empty, null.asInstanceOf[S], Map.empty, Set.empty)
}

/**
 * Keeps the state of a petri net instance.
 */
case class Instance[P[_], T[_, _], S](
    process: PetriNet[P[_], T[_, _]],
    sequenceNr: Long,
    marking: Marking[P],
    state: S,
    jobs: Map[Long, Job[P, T, S, _]],
    receivedCorrelationIds: Set[String]) {

  /**
   * The marking that is already used by running jobs
   */
  lazy val reservedMarking: Marking[P] = jobs.map { case (id, job) ⇒ job.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

  /**
   * The marking that is available for new jobs
   */
  lazy val availableMarking: Marking[P] = marking |-| reservedMarking

  def activeJobs: Iterable[Job[P, T, S, _]] = jobs.values.filter(_.isActive)

  def isBlockedReason(transition: T[_, _]): Option[String] = jobs.values.map {
    case Job(_, _, _, `transition`, _, _, Some(ExceptionState(_, _, reason, _))) ⇒
      Some(s"Transition '$transition' is blocked because it failed previously with: $reason")
    case Job(_, _, _, t, _, _, Some(ExceptionState(_, _, reason, ExceptionStrategy.Fatal))) ⇒
      Some(s"Transition '$t' caused a Fatal exception")
    case _ ⇒ None
  }.find(_.isDefined).flatten

  def nextJobId(): Long = Random.nextLong()
}
