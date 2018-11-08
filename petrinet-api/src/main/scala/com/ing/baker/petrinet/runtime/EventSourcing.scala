package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api._

object EventSourcing {

  sealed trait Event

  sealed trait TransitionEvent extends Event {
    val jobId: Long
    val transitionId: Long
  }

  /**
   * An event describing the fact that a transition has fired in the petri net process.
   */
  case class TransitionFiredEvent(
     override val jobId: Long,
     override val transitionId: Long,
     correlationId: Option[String],
     timeStarted: Long,
     timeCompleted: Long,
     consumed: Marking[Long],
     produced: Marking[Long],
     output: Any) extends TransitionEvent

  /**
   * An event describing the fact that a transition failed to fire.
   */
  case class TransitionFailedEvent(
    override val jobId: Long,
    override val transitionId: Long,
    correlationId: Option[String],
    timeStarted: Long,
    timeFailed: Long,
    consume: Marking[Long],
    input: Any,
    failureReason: String,
    exceptionStrategy: ExceptionStrategy) extends TransitionEvent

  /**
    * An event describing the fact that an instance was initialized.
    */
  case class InitializedEvent(
     marking: Marking[Long],
     state: Any) extends Event

  def apply[P : Identifiable, T : Identifiable, S, E](sourceFn: T ⇒ (S ⇒ E ⇒ S)): Instance[P, T, S] ⇒ Event ⇒ Instance[P, T, S] = instance ⇒ {
    case InitializedEvent(initial, initialState) ⇒

      val initialMarking: Marking[P] = initial.unmarshall(instance.process.places)

      Instance[P, T, S](instance.process, 1, initialMarking, initialState.asInstanceOf[S], Map.empty, Set.empty)
    case e: TransitionFiredEvent ⇒

      val transition = instance.process.transitions.getById(e.transitionId)
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[P] = e.consumed.unmarshall(instance.process.places)
      val produced: Marking[P] = e.produced.unmarshall(instance.process.places)

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )
    case e: TransitionFailedEvent ⇒
      val transition = instance.process.transitions.getById(e.transitionId)

      val consumed: Marking[P] = e.consume.unmarshall(instance.process.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[P, T, S](e.jobId, e.correlationId, instance.state, transition, consumed, e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[P, T, S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[P, T, S](jobs = instance.jobs + (job.id -> updatedJob))
  }
}
