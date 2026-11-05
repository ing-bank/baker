package com.ing.baker.runtime.akka.actor.process_instance

import com.ing.baker.il.petrinet.Transition
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.Event
import com.ing.baker.runtime.akka.actor.process_instance.internal.Instance
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging
import org.apache.pekko.NotUsed
import org.apache.pekko.actor.ActorSystem
import org.apache.pekko.event.{DiagnosticLoggingAdapter, Logging}
import org.apache.pekko.persistence.query.scaladsl.CurrentEventsByPersistenceIdQuery
import org.apache.pekko.persistence.{PersistentActor, RecoveryCompleted}
import org.apache.pekko.sensors.actor.PersistentActorMetrics
import org.apache.pekko.stream.scaladsl.Source
import scalapb.GeneratedMessage

object ProcessInstanceEventSourcingPekko extends LazyLogging {

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

abstract class ProcessInstanceEventSourcingPekko(
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
    trackAndLogEventSize(serializedEvent.serializedSize)

    persist(serializedEvent) { _ => fn(e) }
  }

  def persistAllEvents[O](instance: Instance[RecipeInstanceState], events: List[Event])(fn: List[Event] => O): Unit = {
    val serializedEvents = events.map {e => serializer.serializeEvent(e)(instance)}
    serializedEvents.foreach(event => trackAndLogEventSize(event.serializedSize))

    persistAll(serializedEvents) { _ -> fn(events) }
  }

  private var recoveringState: Instance[RecipeInstanceState] = Instance.uninitialized[RecipeInstanceState](petriNet)

  private def applyToRecoveringState(e: GeneratedMessage with AnyRef): Unit = {
    val eventSize = e.serializedSize
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
