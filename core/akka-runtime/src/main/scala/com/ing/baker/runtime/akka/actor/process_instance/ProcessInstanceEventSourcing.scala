package com.ing.baker.runtime.akka.actor.process_instance

import akka.NotUsed
import akka.actor.{ActorSystem, NoSerializationVerificationNeeded}
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.persistence.query.scaladsl.CurrentEventsByPersistenceIdQuery
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.sensors.actor.PersistentActorMetrics
import akka.stream.scaladsl.Source
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.Event
import com.ing.baker.runtime.akka.actor.process_instance.internal.{ExceptionState, ExceptionStrategy, Instance, Job}
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging
import scalapb.GeneratedMessage

object ProcessInstanceEventSourcing extends LazyLogging {

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
    * An event describing the fact that a transition failed but was continued with a given event
    * This does not consume the input and puts the transition in a blocked state but does create the output.
    */
  case class TransitionFailedWithOutputEvent(override val jobId: Long,
                                    override val transitionId: Id,
                                    correlationId: Option[String],
                                    timeStarted: Long,
                                    timeCompleted: Long,
                                    consumed: Marking[Id],
                                    produced: Marking[Id],
                                    output: Any) extends TransitionEvent


  /**
   * An event describing the fact that a transition failed but was continued with a given event
   * This does not consume the input and puts the transition in a blocked state but does create the output.
   */
  case class TransitionFailedWithFunctionalOutputEvent(override val jobId: Long,
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
    * An event describing the fact that a transition has been delayed.
    */
  case class TransitionDelayed(override val jobId: Long,
                               override val transitionId: Id,
                               consumed: Marking[Id]) extends TransitionEvent

  /**
    * An event describing the fact that a transition has been fired after its delay.
    */
  case class DelayedTransitionFired(override val jobId: Long,
                                    override val transitionId: Id,
                                    timeCompleted: Long,
                                    produced: Marking[Id],
                                    output: Any) extends TransitionEvent

  /**
    * An event describing the fact that an instance was initialized.
    */
  case class InitializedEvent(marking: Marking[Id],
                              state: Any) extends Event

  /**
    * An event that describes the metaData being updated
    * @param metaData
    */
  case class MetaDataAdded(metaData: Map[String, String]) extends Event

  /**
   * An event that describes a listener being added for process completion.
   * @param listenerPath The serialized path of the listener actor.
   */
  case class CompletionListenerAdded(listenerPath: String) extends Event

  /**
   * An event that describes a listener being added for a specific event occurrence.
   * @param eventName The name of the event to listen for.
   * @param listenerPath The serialized path of the listener actor.
   */
  case class EventListenerAdded(eventName: String, listenerPath: String) extends Event

  /**
   * An event that signifies that all completion listeners have been notified and should be removed.
   */
  case class CompletionListenersRemoved() extends Event

  /**
   * An event that signifies that all listeners for a specific event have been notified and should be removed.
   * @param eventName The event for which listeners are removed.
   */
  case class EventListenersRemoved(eventName: String) extends Event

  def apply[S, E](sourceFn: (Long, Transition) => (S => E => S)): Instance[S] => Event => Instance[S] = instance => {
    case InitializedEvent(initial, initialState) =>

      val initialMarking: Marking[Place] = initial.unmarshall(instance.petriNet.places)

      Instance[S](instance.petriNet, 1, initialMarking, Map.empty, initialState.asInstanceOf[S], Map.empty, Set.empty)

    case e: TransitionFiredEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )

    case e: TransitionFailedWithOutputEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[S](e.jobId, e.correlationId, instance.state, transition, consumed, null, None)
      })
      val updatedJob: Job[S] = job.copy(failure = Some(ExceptionState(0, 1, "Blocked after FireEvent retry strategy", ExceptionStrategy.BlockTransition)))

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = instance.marking |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs + (job.id -> updatedJob)
      )

    case e: TransitionFailedWithFunctionalOutputEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )

    case e: TransitionFailedEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)

      val consumed: Marking[Place] = e.consume.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[S](e.jobId, e.correlationId, instance.state, transition, consumed, e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[S](jobs = instance.jobs + (job.id -> updatedJob))

    case e: TransitionDelayed =>
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)

      val delayedInstanceCount: Int = instance.delayedTransitionIds.getOrElse(e.transitionId, 0)

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed),
        delayedTransitionIds = instance.delayedTransitionIds + (e.transitionId -> (delayedInstanceCount + 1)), //Claim the consumed tokens
        jobs = instance.jobs - e.jobId
      )

    case e: DelayedTransitionFired =>
      val delayedInstanceCount: Int = instance.delayedTransitionIds(e.transitionId)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = instance.marking |+| produced,
        delayedTransitionIds = instance.delayedTransitionIds + (e.transitionId -> (delayedInstanceCount - 1)),
        state = newState
      )

    case e: MetaDataAdded =>
        val newState: S = instance.state match {
          case state: RecipeInstanceState =>
            val newRecipeInstanceMetaData: Map[String, String] = state.recipeInstanceMetadata ++ e.metaData
            //We still add an ingredient for the metaData since this makes it easier to use it during interaction execution
            val newIngredients: Map[String, Value] = state.ingredients +
              (RecipeInstanceMetadataName -> com.ing.baker.types.Converters.toValue(newRecipeInstanceMetaData))
            state.copy(ingredients = newIngredients, recipeInstanceMetadata = newRecipeInstanceMetaData).asInstanceOf[S]
          case state =>
            state
      }
      instance.copy[S](state = newState)

    case e: CompletionListenerAdded =>
      instance.copy(
        completionListenerPaths = instance.completionListenerPaths + e.listenerPath
      )

    case e: EventListenerAdded =>
      val currentListeners = instance.eventListenerPaths.getOrElse(e.eventName, Set.empty)
      val updatedListeners = currentListeners + e.listenerPath
      instance.copy(
        eventListenerPaths = instance.eventListenerPaths + (e.eventName -> updatedListeners)
      )

    case _: CompletionListenersRemoved =>
      instance.copy(
        completionListenerPaths = Set.empty
      )

    case e: EventListenersRemoved =>
      instance.copy(
        eventListenerPaths = instance.eventListenerPaths - e.eventName
      )
  }

  def eventsForInstance(
      processTypeName: String,
      recipeInstanceId: String,
      topology: PetriNet,
      encryption: Encryption,
      readJournal: CurrentEventsByPersistenceIdQuery,
      eventSourceFn: (Long, Transition) => (RecipeInstanceState => EventInstance => RecipeInstanceState))(implicit actorSystem: ActorSystem): Source[(Instance[RecipeInstanceState], Event), NotUsed] = {

    val serializer = new ProcessInstanceSerialization[RecipeInstanceState, EventInstance](AkkaSerializerProvider(actorSystem, encryption))

    val persistentId = ProcessInstance.recipeInstanceId2PersistenceId(processTypeName, recipeInstanceId)
    val src = readJournal.currentEventsByPersistenceId(persistentId, 0, Long.MaxValue)
    val eventSource = ProcessInstanceEventSourcing.apply[RecipeInstanceState, EventInstance](eventSourceFn)

    // TODO: remove null value
    src.scan[(Instance[RecipeInstanceState], Event)]((Instance.uninitialized[RecipeInstanceState](topology), null.asInstanceOf[Event])) {
      case ((instance, _), e) =>
        val serializedEvent = e.event.asInstanceOf[AnyRef]
        val deserializedEvent = serializer.deserializeEvent(serializedEvent)(instance)
        val updatedInstance = eventSource.apply(instance)(deserializedEvent)
        (updatedInstance, deserializedEvent)
    }.drop(1) // Just to drop the first event 'uninitialized', not interesting for the consumers.
  }
}

abstract class ProcessInstanceEventSourcing(
    val petriNet: PetriNet,
    encryption: Encryption,
    eventSourceFn: (Long, Transition) => (RecipeInstanceState => EventInstance => RecipeInstanceState)) extends PersistentActor with PersistentActorMetrics {

  protected implicit val system: ActorSystem = context.system

  override val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  private object EventSizingMonitor {
    private def megabytes(mb: Long): Long = mb * 1024 * 1024

    val InitialWarningThreshold: Long = megabytes(20)
    val WarningLogIncrement: Long = megabytes(1)
  }

  private var cumulativeEventLogSize: Long = 0L
  private var nextWarningThreshold: Long = EventSizingMonitor.InitialWarningThreshold

  private def trackAndLogEventSize(newEventSize: Int): Unit = {
    cumulativeEventLogSize += newEventSize

    if (hasCrossedWarningThreshold) {
      logLargeEventLogWarning()
      advanceWarningThreshold()
    }
  }

  private def hasCrossedWarningThreshold: Boolean =
    cumulativeEventLogSize >= nextWarningThreshold

  private def logLargeEventLogWarning(): Unit = {
    val sizeInMB = cumulativeEventLogSize / (1024 * 1024)

    val originalMdcBackup = log.mdc
    try {
      log.mdc(originalMdcBackup ++ Map(
        "persistenceId"  -> persistenceId,
        "eventLogSizeMB" -> sizeInMB
      ))
      log.warning(
        s"Process instance '$persistenceId' has a large event log size: " +
          s"$sizeInMB MB. This may impact performance and recovery times."
      )
    } finally {
      log.mdc(originalMdcBackup)
    }
  }

  /**
   * Advances the warning threshold to the next increment.
   * This ensures we don't log on every single subsequent event, only when the next milestone is reached.
   * The loop handles cases where a large batch of events causes the size to cross multiple thresholds at once.
   */
  private def advanceWarningThreshold(): Unit = {
    while (cumulativeEventLogSize >= nextWarningThreshold) {
      nextWarningThreshold += EventSizingMonitor.WarningLogIncrement
    }
  }

  protected val eventSource: Instance[RecipeInstanceState] => Event => Instance[RecipeInstanceState] =
    ProcessInstanceEventSourcing.apply[RecipeInstanceState, EventInstance](eventSourceFn)

  private val serializer = new ProcessInstanceSerialization[RecipeInstanceState, EventInstance](AkkaSerializerProvider(system, encryption))

  def onRecoveryCompleted(state: Instance[RecipeInstanceState]): Unit

  def persistEvent[O](instance: Instance[RecipeInstanceState], e: Event)(fn: Event => O): Unit = {
    val serializedEvent = serializer.serializeEvent(e)(instance)
    trackAndLogEventSize(serializedEvent.toByteArray.length)

    persist(serializedEvent) { _ => fn(e) }
  }

  def persistAllEvents[O](instance: Instance[RecipeInstanceState], events: List[Event])(fn: List[Event] => O): Unit = {
    val serializedEvents = events.map {e => serializer.serializeEvent(e)(instance)}
    serializedEvents.foreach(event => trackAndLogEventSize(event.toByteArray.length))

    persistAll(serializedEvents) { _ -> fn(events) }
  }

  private var recoveringState: Instance[RecipeInstanceState] = Instance.uninitialized[RecipeInstanceState](petriNet)

  private def applyToRecoveringState(e: GeneratedMessage with AnyRef): Unit = {
    val eventSize = e.toByteArray.length
    trackAndLogEventSize(eventSize)

    val deserializedEvent = serializer.deserializeEvent(e)(recoveringState)
    recoveringState = eventSource(recoveringState)(deserializedEvent)
  }

  override def receiveRecover: Receive = {
    case e: protobuf.Initialized => applyToRecoveringState(e)
    case e: protobuf.TransitionFired => applyToRecoveringState(e)
    case e: protobuf.TransitionFailedWithOutput => applyToRecoveringState(e)
    case e: protobuf.TransitionFailedWithFunctionalOutput => applyToRecoveringState(e)
    case e: protobuf.TransitionFailed => applyToRecoveringState(e)
    case e: protobuf.TransitionDelayed => applyToRecoveringState(e)
    case e: protobuf.DelayedTransitionFired => applyToRecoveringState(e)
    case e: protobuf.MetaDataAdded => applyToRecoveringState(e)
    case e: protobuf.CompletionListenerAdded => applyToRecoveringState(e)
    case e: protobuf.EventListenerAdded => applyToRecoveringState(e)
    case e: protobuf.CompletionListenersRemoved => applyToRecoveringState(e)
    case e: protobuf.EventListenersRemoved => applyToRecoveringState(e)
    case RecoveryCompleted =>
      if (recoveringState.sequenceNr > 0)
        onRecoveryCompleted(recoveringState)
  }
}
