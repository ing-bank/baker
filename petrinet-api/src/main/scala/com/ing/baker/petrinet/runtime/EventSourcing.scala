package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api._

import scala.collection.Map

object EventSourcing {

  sealed trait Event

  sealed trait TransitionEvent extends Event {
    val jobId: Long
    val transitionId: Long
  }

  /**
   * An event describing the fact that a transition has fired in the petri net process.
   */
  case class TransitionFiredEvent[P](
     override val jobId: Long,
     override val transitionId: Long,
     correlationId: Option[String],
     timeStarted: Long,
     timeCompleted: Long,
     consumed: Marking[P],
     produced: Marking[P],
     output: Any) extends TransitionEvent

  /**
   * An event describing the fact that a transition failed to fire.
   */
  case class TransitionFailedEvent[P](
    override val jobId: Long,
    override val transitionId: Long,
    correlationId: Option[String],
    timeStarted: Long,
    timeFailed: Long,
    consume: Marking[P],
    input: Any,
    failureReason: String,
    exceptionStrategy: ExceptionStrategy) extends TransitionEvent

  /**
   * An event describing the fact that an instance was initialized.
   */
  case class InitializedEvent[P](
    marking: Marking[P],
    state: Any) extends Event

  def apply[P : Identifiable, T : Identifiable, S, E](sourceFn: T ⇒ (S ⇒ E ⇒ S)): Instance[P, T, S] ⇒ Event ⇒ Instance[P, T, S] = instance ⇒ {
    case InitializedEvent(initialMarking, initialState) ⇒
      Instance[P, T, S](instance.process, 1, initialMarking.asInstanceOf[Marking[P]], initialState.asInstanceOf[S], Map.empty, Set.empty)
    case e: TransitionFiredEvent[_] ⇒

      val transition = instance.process.transitions.getById(e.transitionId)

      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| e.consumed.asInstanceOf[Marking[P]]) |+| e.produced.asInstanceOf[Marking[P]],
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )
    case e: TransitionFailedEvent[_] ⇒
      val transition = instance.process.transitions.getById(e.transitionId)
      val job = instance.jobs.getOrElse(e.jobId, {
        Job[P, T, S](e.jobId, e.correlationId, instance.state, transition, e.consume.asInstanceOf[Marking[P]], e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[P, T, S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[P, T, S](jobs = instance.jobs + (job.id -> updatedJob))
  }
}
