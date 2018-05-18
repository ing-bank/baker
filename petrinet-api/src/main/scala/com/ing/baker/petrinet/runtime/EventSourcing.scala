package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api.Marking

import scala.collection.Map

object EventSourcing {

  sealed trait Event

  sealed trait TransitionEvent[T[_]] extends Event {
    val jobId: Long
    val transition: T[_]
  }

  /**
   * An event describing the fact that a transition has fired in the petri net process.
   */
  case class TransitionFiredEvent[P[_], T[_], E](
    override val jobId: Long,
    override val transition: T[_],
    correlationId: Option[String],
    timeStarted: Long,
    timeCompleted: Long,
    consumed: Marking[P],
    produced: Marking[P],
    output: E) extends TransitionEvent[T]

  /**
   * An event describing the fact that a transition failed to fire.
   */
  case class TransitionFailedEvent[P[_], T[_], I](
    override val jobId: Long,
    override val transition: T[_],
    correlationId: Option[String],
    timeStarted: Long,
    timeFailed: Long,
    consume: Marking[P],
    input: I,
    failureReason: String,
    exceptionStrategy: ExceptionStrategy) extends TransitionEvent[T]

  /**
   * An event describing the fact that an instance was initialized.
   */
  case class InitializedEvent[P[_]](
    marking: Marking[P],
    state: Any) extends Event

  def apply[P[_], T[_], S, E](sourceFn: T[_] ⇒ EventSource[S, E]): Instance[P, T, S] ⇒ Event ⇒ Instance[P, T, S] = instance ⇒ {
    case InitializedEvent(initialMarking, initialState) ⇒
      Instance[P, T, S](instance.process, 1, initialMarking.asInstanceOf[Marking[P]], initialState.asInstanceOf[S], Map.empty, Set.empty)
    case e: TransitionFiredEvent[_, _, _] ⇒

      val transition = e.transition.asInstanceOf[T[Any]]
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| e.consumed.asInstanceOf[Marking[P]]) |+| e.produced.asInstanceOf[Marking[P]],
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )
    case e: TransitionFailedEvent[_, _, _] ⇒
      val transition = e.transition.asInstanceOf[T[Any]]
      val job = instance.jobs.getOrElse(e.jobId, {
        Job[P, T, S](e.jobId, e.correlationId, instance.state, transition, e.consume.asInstanceOf[Marking[P]], e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[P, T, S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[P, T, S](jobs = instance.jobs + (job.id -> updatedJob))
  }
}
