package com.ing.baker.runtime.actor.process_instance

import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.serialization.SerializationExtension
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.process_instance.internal.{ExceptionState, ExceptionStrategy, Instance, Job}
import com.ing.baker.runtime.actor.serialization.{Encryption, ProtoEventAdapterImpl}
import ProcessInstanceEventSourcing._
import akka.actor.NoSerializationVerificationNeeded

object ProcessInstanceEventSourcing {

  sealed trait Event extends NoSerializationVerificationNeeded

  sealed trait TransitionEvent extends Event {
    val jobId: Long
    val transitionId: Id
  }

  /**
    * An event describing the fact that a transition has fired in the petri net process.
    */
  case class TransitionFiredEvent(override val jobId: Long,
                                  override val transitionId: Id,
                                  correlationId: Option[String],
                                  timeStarted: Long,
                                  timeCompleted: Long,
                                  consumed: Marking[Id],
                                  produced: Marking[Id],
                                  output: Any) extends TransitionEvent

  /**
    * An event describing the fact that a transition failed to fire.
    */
  case class TransitionFailedEvent(override val jobId: Long,
                                   override val transitionId: Id,
                                   correlationId: Option[String],
                                   timeStarted: Long,
                                   timeFailed: Long,
                                   consume: Marking[Id],
                                   input: Any,
                                   failureReason: String,
                                   exceptionStrategy: ExceptionStrategy) extends TransitionEvent

  /**
    * An event describing the fact that an instance was initialized.
    */
  case class InitializedEvent(marking: Marking[Id],
                              state: Any) extends Event

  def apply[P : Identifiable, T : Identifiable, S, E](sourceFn: T ⇒ (S ⇒ E ⇒ S)): Instance[P, T, S] ⇒ Event ⇒ Instance[P, T, S] = instance ⇒ {
    case InitializedEvent(initial, initialState) ⇒

      val initialMarking: Marking[P] = initial.unmarshall(instance.petriNet.places)

      Instance[P, T, S](instance.petriNet, 1, initialMarking, initialState.asInstanceOf[S], Map.empty, Set.empty)
    case e: TransitionFiredEvent ⇒

      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[P] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[P] = e.produced.unmarshall(instance.petriNet.places)

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )
    case e: TransitionFailedEvent ⇒
      val transition = instance.petriNet.transitions.getById(e.transitionId)

      val consumed: Marking[P] = e.consume.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[P, T, S](e.jobId, e.correlationId, instance.state, transition, consumed, e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[P, T, S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[P, T, S](jobs = instance.jobs + (job.id -> updatedJob))
  }

}

abstract class ProcessInstanceEventSourcing[P : Identifiable, T : Identifiable, S, E](
    val petriNet: PetriNet[P, T],
    encryption: Encryption,
    eventSourceFn: T => (S => E => S)) extends PersistentActor {

  implicit val system = context.system

  val eventSource = ProcessInstanceEventSourcing.apply[P, T, S, E](eventSourceFn)

  private val protoEventAdapter = new ProtoEventAdapterImpl(SerializationExtension.get(system), encryption)
  private val serializer = new ProcessInstanceSerialization[P, T, S, E](protoEventAdapter)

  def onRecoveryCompleted(state: Instance[P, T, S])

  def persistEvent[O](instance: Instance[P, T, S], e: Event)(fn: Event => O): Unit = {
    val serializedEvent = serializer.serializeEvent(e)(instance)
    persist(serializedEvent) { persisted => fn(e) }
  }

  private var recoveringState: Instance[P, T, S] = Instance.uninitialized[P, T, S](petriNet)

  private def applyToRecoveringState(e: AnyRef) = {
    val deserializedEvent = serializer.deserializeEvent(e)(recoveringState)
    recoveringState = eventSource(recoveringState)(deserializedEvent)
  }

  override def receiveRecover: Receive = {
    case e: protobuf.Initialized      ⇒ applyToRecoveringState(e)
    case e: protobuf.TransitionFired  ⇒ applyToRecoveringState(e)
    case e: protobuf.TransitionFailed ⇒ applyToRecoveringState(e)
    case RecoveryCompleted ⇒
      if (recoveringState.sequenceNr > 0)
        onRecoveryCompleted(recoveringState)
  }
}
