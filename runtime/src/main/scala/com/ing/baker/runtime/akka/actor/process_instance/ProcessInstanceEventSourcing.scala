package com.ing.baker.runtime.akka.actor.process_instance

import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.internal.{ExceptionState, ExceptionStrategy, Instance, Job}
import ProcessInstanceEventSourcing._
import akka.NotUsed
import akka.actor.{ActorSystem, NoSerializationVerificationNeeded}
import akka.persistence.query.scaladsl.CurrentEventsByPersistenceIdQuery
import akka.stream.scaladsl.Source
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.serialization.Encryption

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

  def eventsForInstance[P : Identifiable, T : Identifiable, S, E](
      processTypeName: String,
      recipeInstanceId: String,
      topology: PetriNet[P, T],
      encryption: Encryption,
      readJournal: CurrentEventsByPersistenceIdQuery,
      eventSourceFn: T ⇒ (S ⇒ E ⇒ S))(implicit actorSystem: ActorSystem): Source[(Instance[P, T, S], Event), NotUsed] = {

    val serializer = new ProcessInstanceSerialization[P, T, S, E](AkkaSerializerProvider(actorSystem, encryption))

    val persistentId = ProcessInstance.recipeInstanceId2PersistenceId(processTypeName, recipeInstanceId)
    val src = readJournal.currentEventsByPersistenceId(persistentId, 0, Long.MaxValue)
    val eventSource = ProcessInstanceEventSourcing.apply[P, T, S, E](eventSourceFn)

    // TODO: remove null value
    src.scan[(Instance[P, T, S], Event)]((Instance.uninitialized[P, T, S](topology), null.asInstanceOf[Event])) {
      case ((instance, _), e) ⇒
        val serializedEvent = e.event.asInstanceOf[AnyRef]
        val deserializedEvent = serializer.deserializeEvent(serializedEvent)(instance)
        val updatedInstance = eventSource.apply(instance)(deserializedEvent)
        (updatedInstance, deserializedEvent)
    }.drop(1) // Just to drop the first event 'uninitialized', not interesting for the consumers.
  }
}

abstract class ProcessInstanceEventSourcing[P : Identifiable, T : Identifiable, S, E](
    val petriNet: PetriNet[P, T],
    encryption: Encryption,
    eventSourceFn: T => (S => E => S)) extends PersistentActor {

  protected implicit val system: ActorSystem = context.system

  protected val eventSource: Instance[P, T, S] => Event => Instance[P, T, S] =
    ProcessInstanceEventSourcing.apply[P, T, S, E](eventSourceFn)

  private val serializer = new ProcessInstanceSerialization[P, T, S, E](AkkaSerializerProvider(system, encryption))

  def onRecoveryCompleted(state: Instance[P, T, S])

  def persistEvent[O](instance: Instance[P, T, S], e: Event)(fn: Event => O): Unit = {
    val serializedEvent = serializer.serializeEvent(e)(instance)
    persist(serializedEvent) { persisted => fn(e) }
  }

  private var recoveringState: Instance[P, T, S] = Instance.uninitialized[P, T, S](petriNet)

  private def applyToRecoveringState(e: AnyRef): Unit = {
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
