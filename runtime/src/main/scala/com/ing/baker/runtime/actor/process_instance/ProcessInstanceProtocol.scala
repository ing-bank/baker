package com.ing.baker.runtime.actor.process_instance

import com.ing.baker.petrinet.api.{Identifiable, Marking, MultiSet}
import com.ing.baker.runtime.actor.serialization.BakerProtoMessage

/**
 * Describes the messages to and from a PetriNetInstance actor.
 */
object ProcessInstanceProtocol {

  /**
   * Type alias for marking data.
   */
  type MarkingData = Map[Long, MultiSet[_]]

  def marshal[P](marking: Marking[P])(implicit identifiable: Identifiable[P]): MarkingData = marking.map {
    case (p, mset) ⇒ identifiable(p).value -> mset
  }.toMap

  def unmarshal[P](data: MarkingData, placeById: Long ⇒ P): Marking[P] = data.map {
    case (id, mset) ⇒ placeById(id) -> mset.asInstanceOf[MultiSet[Any]]
  }

  /**
   * A common trait for all commands to a petri net instance.
   */
  sealed trait Command extends BakerProtoMessage

  /**
   * Command to request the current state of the petri net instance.
   */
  case object GetState extends Command

  /**
    * Command to stop and optionally delete the process instance.
    */
  case class Stop(delete: Boolean = false) extends Command

  object Initialize {

    def apply[P : Identifiable](marking: Marking[P]): Initialize = Initialize(marshal[P](marking), null)

    def apply[P : Identifiable](marking: Marking[P], state: Any): Initialize = Initialize(marshal[P](marking), state)
  }

  /**
   * Command to initialize a petri net instance.
   */
  case class Initialize(marking: MarkingData, state: Any) extends Command

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
  sealed trait Response extends BakerProtoMessage

  /**
   * A response send in case any other command then 'Initialize' is sent to the actor in unitialized state.
   *
   * @param processId The identifier of the uninitialized actor.
   */
  case class Uninitialized(processId: String) extends Response

  /**
   * Returned in case a second Initialize is send after a first is processed
   */
  case class AlreadyInitialized(processId: String) extends Response

  /**
    * Indicates that the received FireTransition command with a specific correlation id was already received.
    */
  case class AlreadyReceived(correlationId: String) extends Response

  object Initialized {

    def apply[P : Identifiable](marking: Marking[P]): Initialized = Initialized(marshal[P](marking), null)

    def apply[P : Identifiable](marking: Marking[P], state: Any): Initialized = Initialized(marshal[P](marking), state)
  }

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
    state: InstanceState,
    newJobsIds: Set[Long],
    output: Any) extends TransitionResponse

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

  sealed trait ExceptionStrategy

  object ExceptionStrategy {

    case object Fatal extends ExceptionStrategy

    case object BlockTransition extends ExceptionStrategy

    case class RetryWithDelay(delay: Long) extends ExceptionStrategy {
      require(delay > 0, "Delay must be greater then zero")
    }

    case class Continue(marking: MarkingData, output: Any) extends ExceptionStrategy
  }


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
      case Some(ExceptionState(_, _, ExceptionStrategy.RetryWithDelay(_))) ⇒ true
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
