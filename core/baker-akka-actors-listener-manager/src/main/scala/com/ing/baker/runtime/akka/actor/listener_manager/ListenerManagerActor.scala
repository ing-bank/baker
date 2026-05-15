package com.ing.baker.runtime.akka.actor.listener_manager

import akka.actor.{ActorSelection, Props}
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.sensors.actor.PersistentActorMetrics
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.{Completed, EventOccurred}

object ListenerManagerActor {
  
  /**
   * Create Props for ListenerManagerActor
   * @param recipeInstanceId The recipe instance this manager belongs to
   */
  def props(recipeInstanceId: String): Props =
    Props(new ListenerManagerActor(recipeInstanceId))
  
  def persistenceId(recipeInstanceId: String): String =
    s"listener-manager-$recipeInstanceId"
  
  // Protocol
  sealed trait Command
  
  /**
   * Register a listener for recipe completion.
   * If already completed, listener is notified immediately.
   */
  case class RegisterCompletionListener(listenerPath: String) extends Command
  
  /**
   * Register a listener for a specific event.
   * @param eventName The event to listen for
   * @param listenerPath The actor path to notify
   * @param waitForNext If true, wait for next occurrence even if event already fired
   */
  case class RegisterEventListener(
    eventName: String, 
    listenerPath: String, 
    waitForNext: Boolean = false
  ) extends Command
  
  /**
   * Notify that a specific event has occurred.
   * Triggers notification to all listeners waiting for this event.
   */
  case class NotifyEventOccurred(eventName: String) extends Command
  
  /**
   * Notify that the recipe has completed.
   * Triggers notification to all completion listeners.
   */
  case object NotifyCompleted extends Command
  
  // Internal events for event sourcing
  sealed trait Event
  
  case class CompletionListenerAdded(listenerPath: String) extends Event
  case class EventListenerAdded(eventName: String, listenerPath: String) extends Event
  case class CompletionNotified() extends Event
  case class EventNotified(eventName: String) extends Event
  
  // State
  case class State(
    sequenceNr: Long,
    recipeInstanceId: String,
    completionListeners: Set[String],
    eventListeners: Map[String, Set[String]],
    hasCompleted: Boolean,
    firedEvents: Set[String]
  ) {
    def hasActiveListeners: Boolean = 
      completionListeners.nonEmpty || eventListeners.nonEmpty
  }
  
  object State {
    def empty(recipeInstanceId: String): State =
      State(
        sequenceNr = 0,
        recipeInstanceId = recipeInstanceId,
        completionListeners = Set.empty,
        eventListeners = Map.empty,
        hasCompleted = false,
        firedEvents = Set.empty
      )
  }
}

/**
 * Actor managing listener registrations and notifications for a recipe instance.
 * 
 * This actor handles:
 * - Completion listener registration and notification
 * - Event listener registration and notification
 * - Immediate notification when already completed/fired
 * - Persistent state to survive restarts
 * 
 * Extracted from ProcessInstance to separate concerns and reduce complexity.
 */
class ListenerManagerActor(recipeInstanceId: String) 
  extends PersistentActor 
  with PersistentActorMetrics {
  
  import ListenerManagerActor._
  
  override def persistenceId: String = 
    ListenerManagerActor.persistenceId(recipeInstanceId)
  
  private var state: State = State.empty(recipeInstanceId)
  
  override def receiveRecover: Receive = {
    case event: Event =>
      state = applyEvent(state, event)
    
    case RecoveryCompleted =>
      log.debug(s"ListenerManagerActor recovery completed for $recipeInstanceId " +
        s"(completed=${state.hasCompleted}, firedEvents=${state.firedEvents.size}, " +
        s"completionListeners=${state.completionListeners.size}, " +
        s"eventListeners=${state.eventListeners.values.map(_.size).sum})")
  }
  
  override def receiveCommand: Receive = {
    
    case RegisterCompletionListener(listenerPath) =>
      if (state.hasCompleted) {
        // Already completed - notify immediately
        log.debug(s"Completion already occurred, notifying $listenerPath immediately")
        notifyListener(listenerPath, Completed)
      } else {
        // Not yet completed - persist and register
        val event = CompletionListenerAdded(listenerPath)
        persist(event) { evt =>
          state = applyEvent(state, evt)
          log.debug(s"Completion listener registered: $listenerPath")
        }
      }
    
    case RegisterEventListener(eventName, listenerPath, waitForNext) =>
      if (!waitForNext && state.firedEvents.contains(eventName)) {
        // Event already occurred - notify immediately
        log.debug(s"Event '$eventName' already fired, notifying $listenerPath immediately")
        notifyListener(listenerPath, EventOccurred)
      } else {
        // Event not yet occurred - persist and register
        val event = EventListenerAdded(eventName, listenerPath)
        persist(event) { evt =>
          state = applyEvent(state, evt)
          log.debug(s"Event listener registered: $listenerPath for event '$eventName'")
        }
      }
    
    case NotifyEventOccurred(eventName) =>
      val listeners = state.eventListeners.getOrElse(eventName, Set.empty)
      if (listeners.nonEmpty) {
        // Notify all registered listeners
        log.debug(s"Notifying ${listeners.size} listeners for event '$eventName'")
        listeners.foreach { path =>
          notifyListener(path, EventOccurred)
        }
        // Persist the notification and cleanup
        val event = EventNotified(eventName)
        persist(event) { evt =>
          state = applyEvent(state, evt)
        }
      } else {
        // No listeners, but still mark as fired
        val event = EventNotified(eventName)
        persist(event) { evt =>
          state = applyEvent(state, evt)
          log.debug(s"Event '$eventName' marked as fired (no listeners)")
        }
      }
    
    case NotifyCompleted =>
      if (state.completionListeners.nonEmpty) {
        // Notify all completion listeners
        log.debug(s"Notifying ${state.completionListeners.size} completion listeners")
        state.completionListeners.foreach { path =>
          notifyListener(path, Completed)
        }
        // Persist the completion
        val event = CompletionNotified()
        persist(event) { evt =>
          state = applyEvent(state, evt)
        }
      } else if (!state.hasCompleted) {
        // Mark as completed even if no listeners
        val event = CompletionNotified()
        persist(event) { evt =>
          state = applyEvent(state, evt)
          log.debug(s"Recipe instance completed (no listeners)")
        }
      }
  }
  
  private def notifyListener(listenerPath: String, message: Any): Unit = {
    val selection: ActorSelection = context.actorSelection(listenerPath)
    selection ! message
  }
  
  private def applyEvent(state: State, event: Event): State = {
    event match {
      case CompletionListenerAdded(listenerPath) =>
        state.copy(
          sequenceNr = state.sequenceNr + 1,
          completionListeners = state.completionListeners + listenerPath
        )
      
      case EventListenerAdded(eventName, listenerPath) =>
        val currentListeners = state.eventListeners.getOrElse(eventName, Set.empty)
        state.copy(
          sequenceNr = state.sequenceNr + 1,
          eventListeners = state.eventListeners + (eventName -> (currentListeners + listenerPath))
        )
      
      case CompletionNotified() =>
        state.copy(
          sequenceNr = state.sequenceNr + 1,
          hasCompleted = true,
          completionListeners = Set.empty  // Clear listeners after notification
        )
      
      case EventNotified(eventName) =>
        state.copy(
          sequenceNr = state.sequenceNr + 1,
          firedEvents = state.firedEvents + eventName,
          eventListeners = state.eventListeners - eventName  // Remove listeners for this event
        )
    }
  }
}
