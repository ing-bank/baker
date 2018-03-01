package com.ing.baker.runtime.actor.process_instance

import com.ing.baker.petrinet.api.{HMap, Identifiable, Marking, MultiSet}
import com.ing.baker.petrinet.runtime.ExceptionStrategy
import com.ing.baker.petrinet.runtime.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.actor.InternalBakerMessage

/**
 * Describes the messages to and from a PetriNetInstance actor.
 */
object ProcessInstanceProtocol {

  /**
   * Type alias for marking data.
   */
  type MarkingData = Map[Long, MultiSet[_]]

  implicit def fromExecutionInstance[P[_], T[_, _], S](instance: com.ing.baker.petrinet.runtime.Instance[P, T, S])(implicit placeIdentifier: Identifiable[P[_]], transitionIdentifier: Identifiable[T[_, _]]): InstanceState =
    InstanceState(instance.sequenceNr, marshal[P](instance.marking), instance.state, instance.jobs.mapValues(fromExecutionJob(_)).map(identity))

  implicit def fromExecutionJob[P[_], T[_, _], S, E](job: com.ing.baker.petrinet.runtime.Job[P, T, S, E])(implicit placeIdentifier: Identifiable[P[_]], transitionIdentifier: Identifiable[T[_, _]]): JobState =
    JobState(job.id, transitionIdentifier(job.transition.asInstanceOf[T[_, _]]).value, marshal(job.consume), job.input, job.failure.map(fromExecutionExceptionState))

  implicit def fromExecutionExceptionState(exceptionState: com.ing.baker.petrinet.runtime.ExceptionState): ExceptionState =
    ExceptionState(exceptionState.failureCount, exceptionState.failureReason, exceptionState.failureStrategy)

  def marshal[P[_]](marking: Marking[P])(implicit identifiable: Identifiable[P[_]]): MarkingData = marking.map {
    case (p, mset) ⇒ identifiable(p).value -> mset
  }.toMap

  def unmarshal[P[_]](data: MarkingData, placeById: Long ⇒ P[_]): Marking[P] = HMap[P, MultiSet](data.map {
    case (id, mset) ⇒ placeById(id) -> mset
  }.toMap)

  /**
   * A common trait for all commands to a petri net instance.
   */
  sealed trait Command extends InternalBakerMessage

  /**
   * Command to request the current state of the petri net instance.
   */
  case object GetState extends Command

  /**
    * Command to stop and optionally delete the process instance.
    */
  case class Stop(delete: Boolean = false) extends Command

  object Initialize {

    def apply[P[_]](marking: Marking[P])(implicit placeIdentifier: Identifiable[P[_]]): Initialize = Initialize(marshal[P](marking), ())
  }

  /**
   * Command to initialize a petri net instance.
   */
  case class Initialize(marking: MarkingData, state: Any) extends Command

  object FireTransition {

    def apply[T[_, _], I](t: T[I, _], input: I)(implicit transitionIdentifier: Identifiable[T[_, _]]): FireTransition = FireTransition(transitionIdentifier(t.asInstanceOf[T[_, _]]).value, input, None)

    def apply[T[_, _]](t: T[Unit, _])(implicit transitionIdentifier: Identifiable[T[_, _]]): FireTransition = FireTransition(transitionIdentifier(t.asInstanceOf[T[_, _]]).value, (), None)
  }

  /**
   * Command to fire a specific transition with input.
   */
  case class FireTransition(
    transitionId: Long,
    input: Any,
    correlationId: Option[String] = None) extends Command

  /**
   * A common trait for all responses coming from a petri net instance.
   */
  sealed trait Response extends InternalBakerMessage

  /**
   * A response send in case any other command then 'Initialize' is sent to the actor in unitialized state.
   *
   * @param id The identifier of the uninitialized actor.
   */
  case class Uninitialized(id: String) extends Response

  /**
   * Returned in case a second Initialize is send after a first is processed
   */
  case object AlreadyInitialized extends Response

  /**
    * Indicates that the received FireTransition command with a specific correlation id was already received.
    */
  case class AlreadyReceived(correlationId: String) extends Response

  /**
   * A response indicating that the instance has been initialized in a certain state.
   *
   * This message is only send in response to an Initialize message.
   */
  case class Initialized(
    marking: MarkingData,
    state: Any) extends Response

  /**
   * Any message that is a response to a FireTransition command.
   */
  sealed trait TransitionResponse extends Response {
    val transitionId: Long
  }

  /**
   * Response indicating that a transition has fired successfully
   */
  case class TransitionFired(
    jobId: Long,
    override val transitionId: Long,
    correlationId: Option[String],
    consumed: MarkingData,
    produced: MarkingData,
    result: InstanceState,
    newJobsIds: Set[Long]) extends TransitionResponse

  /**
   * Response indicating that a transition has failed.
   */
  case class TransitionFailed(
    jobId: Long,
    override val transitionId: Long,
    correlationId: Option[String],
    consume: MarkingData,
    input: Any,
    reason: String,
    strategy: ExceptionStrategy) extends TransitionResponse

  /**
   * Response indicating that the transition could not be fired because it is not enabled.
   */
  case class TransitionNotEnabled(
    override val transitionId: Long,
    reason: String) extends TransitionResponse

  /**
   * The exception state of a transition.
   */
  case class ExceptionState(
    failureCount: Int,
    failureReason: String,
    failureStrategy: ExceptionStrategy)

  /**
   * Response containing the state of the `Job`.
   */
  case class JobState(
      id: Long,
      transitionId: Long,
      consumedMarking: MarkingData,
      input: Any,
      exceptionState: Option[ExceptionState]) {

    def isActive: Boolean = exceptionState match {
      case Some(ExceptionState(_, _, RetryWithDelay(_))) ⇒ true
      case None                                          ⇒ true
      case _                                             ⇒ false
    }
  }

  /**
   * Response containing the state of the process.
   */
  case class InstanceState(
    sequenceNr: Long,
    marking: MarkingData,
    state: Any,
    jobs: Map[Long, JobState]) extends Response
}
