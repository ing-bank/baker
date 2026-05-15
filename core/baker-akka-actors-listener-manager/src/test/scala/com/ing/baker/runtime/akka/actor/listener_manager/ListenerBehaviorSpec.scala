package com.ing.baker.runtime.akka.actor.listener_manager

import akka.testkit.TestProbe
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.{Completed, EventOccurred}
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike

import scala.concurrent.duration._

/**
 * Comprehensive behavior tests for listener management.
 * 
 * This trait defines all expected listener behavior that can be mixed into tests for:
 * 1. Current ProcessInstance implementation (baseline)
 * 2. New ListenerManagerActor implementation (must match baseline)
 * 
 * By using this trait, we ensure both implementations have identical behavior
 * and prevent any regressions during the extraction.
 * 
 * Test implementations must provide:
 * - Methods to register listeners
 * - Methods to trigger notifications
 * - Methods to query state
 * - TestProbe factory for creating mock listeners
 */
trait ListenerBehaviorSpec extends AnyWordSpecLike with Matchers {
  
  // Abstract methods that implementations must provide
  
  /**
   * Register a listener for recipe completion.
   * The listener should be notified when the recipe completes execution.
   */
  def registerCompletionListener(listenerProbe: TestProbe): Unit
  
  /**
   * Register a listener for a specific event occurrence.
   * @param eventName The name of the event to listen for
   * @param listenerProbe The probe that should receive notification
   * @param waitForNext If true, wait for next occurrence even if event already fired
   */
  def registerEventListener(eventName: String, listenerProbe: TestProbe, waitForNext: Boolean = false): Unit
  
  /**
   * Trigger notification that a specific event has occurred.
   * Should notify all listeners waiting for this event.
   */
  def notifyEventOccurred(eventName: String): Unit
  
  /**
   * Trigger notification that the recipe has completed.
   * Should notify all completion listeners.
   */
  def notifyCompleted(): Unit
  
  /**
   * Check if the recipe is marked as completed.
   */
  def isCompleted: Boolean
  
  /**
   * Check if a specific event has been fired/occurred.
   */
  def hasFiredEvent(eventName: String): Boolean
  
  /**
   * Create a new test probe for listener tests.
   * Implementations provide this via their actor system.
   */
  def createListenerProbe(): TestProbe
  
  /**
   * Default timeout for expectNoMessage checks
   */
  val noMsgTimeout: FiniteDuration = 200.millis
  
  "Completion Listener Management" should {
    
    "immediately notify listener if already completed" in {
      val listener = createListenerProbe()
      
      // Complete first
      notifyCompleted()
      isCompleted shouldBe true
      
      // Then register listener
      registerCompletionListener(listener)
      
      // Should receive immediate notification
      listener.expectMsg(Completed)
    }
    
    "register listener and notify when completion occurs" in {
      val listener = createListenerProbe()
      
      // Register listener before completion
      registerCompletionListener(listener)
      
      // Should not receive anything yet
      listener.expectNoMessage(noMsgTimeout)
      
      // Trigger completion
      notifyCompleted()
      
      // Should receive notification
      listener.expectMsg(Completed)
      isCompleted shouldBe true
    }
    
    "notify multiple completion listeners" in {
      val listener1 = createListenerProbe()
      val listener2 = createListenerProbe()
      val listener3 = createListenerProbe()
      
      // Register multiple listeners
      registerCompletionListener(listener1)
      registerCompletionListener(listener2)
      registerCompletionListener(listener3)
      
      // None should have received notification yet
      listener1.expectNoMessage(noMsgTimeout)
      listener2.expectNoMessage(noMsgTimeout)
      listener3.expectNoMessage(noMsgTimeout)
      
      // Trigger completion
      notifyCompleted()
      
      // All should receive notification
      listener1.expectMsg(Completed)
      listener2.expectMsg(Completed)
      listener3.expectMsg(Completed)
    }
    
    "only notify each completion listener once" in {
      val listener = createListenerProbe()
      
      // Register listener
      registerCompletionListener(listener)
      
      // Trigger completion
      notifyCompleted()
      listener.expectMsg(Completed)
      
      // Register same listener again (after completion)
      registerCompletionListener(listener)
      
      // Should receive immediate notification but only one more
      listener.expectMsg(Completed)
      listener.expectNoMessage(noMsgTimeout)
    }
    
    "handle completion notification when no listeners registered" in {
      // Should not crash
      noException should be thrownBy {
        notifyCompleted()
      }
      isCompleted shouldBe true
    }
  }
  
  "Event Listener Management" should {
    
    "immediately notify listener if event already fired (waitForNext=false)" in {
      val listener = createListenerProbe()
      val eventName = "TestEvent"
      
      // Fire event first
      notifyEventOccurred(eventName)
      hasFiredEvent(eventName) shouldBe true
      
      // Then register listener with waitForNext=false
      registerEventListener(eventName, listener, waitForNext = false)
      
      // Should receive immediate notification
      listener.expectMsg(EventOccurred)
    }
    
    "wait for next occurrence if event already fired (waitForNext=true)" in {
      val listener = createListenerProbe()
      val eventName = "TestEvent"
      
      // Fire event first
      notifyEventOccurred(eventName)
      hasFiredEvent(eventName) shouldBe true
      
      // Register listener with waitForNext=true
      registerEventListener(eventName, listener, waitForNext = true)
      
      // Should NOT receive immediate notification
      listener.expectNoMessage(noMsgTimeout)
      
      // Fire event again
      notifyEventOccurred(eventName)
      
      // Now should receive notification
      listener.expectMsg(EventOccurred)
    }
    
    "register listener and notify when event occurs" in {
      val listener = createListenerProbe()
      val eventName = "TestEvent"
      
      // Register listener before event
      registerEventListener(eventName, listener)
      
      // Should not receive anything yet
      listener.expectNoMessage(noMsgTimeout)
      
      // Trigger event
      notifyEventOccurred(eventName)
      
      // Should receive notification
      listener.expectMsg(EventOccurred)
      hasFiredEvent(eventName) shouldBe true
    }
    
    "notify multiple listeners for same event" in {
      val listener1 = createListenerProbe()
      val listener2 = createListenerProbe()
      val listener3 = createListenerProbe()
      val eventName = "TestEvent"
      
      // Register multiple listeners
      registerEventListener(eventName, listener1)
      registerEventListener(eventName, listener2)
      registerEventListener(eventName, listener3)
      
      // None should have received notification yet
      listener1.expectNoMessage(noMsgTimeout)
      listener2.expectNoMessage(noMsgTimeout)
      listener3.expectNoMessage(noMsgTimeout)
      
      // Trigger event
      notifyEventOccurred(eventName)
      
      // All should receive notification
      listener1.expectMsg(EventOccurred)
      listener2.expectMsg(EventOccurred)
      listener3.expectMsg(EventOccurred)
    }
    
    "handle different events independently" in {
      val listenerA = createListenerProbe()
      val listenerB = createListenerProbe()
      
      // Register listeners for different events
      registerEventListener("EventA", listenerA)
      registerEventListener("EventB", listenerB)
      
      // Trigger EventA
      notifyEventOccurred("EventA")
      
      // Only listenerA should be notified
      listenerA.expectMsg(EventOccurred)
      listenerB.expectNoMessage(noMsgTimeout)
      
      // Trigger EventB
      notifyEventOccurred("EventB")
      
      // Only listenerB should be notified
      listenerB.expectMsg(EventOccurred)
      listenerA.expectNoMessage(noMsgTimeout)
    }
    
    "only notify each event listener once per registration" in {
      val listener = createListenerProbe()
      val eventName = "TestEvent"
      
      // Register listener
      registerEventListener(eventName, listener)
      
      // Trigger event
      notifyEventOccurred(eventName)
      listener.expectMsg(EventOccurred)
      
      // Trigger same event again
      notifyEventOccurred(eventName)
      
      // Should NOT receive notification again (listener was removed after first notification)
      listener.expectNoMessage(noMsgTimeout)
    }
    
    "allow re-registration for same event after notification" in {
      val listener = createListenerProbe()
      val eventName = "TestEvent"
      
      // First registration
      registerEventListener(eventName, listener)
      notifyEventOccurred(eventName)
      listener.expectMsg(EventOccurred)
      
      // Re-register after notification (with waitForNext=true to wait for next occurrence)
      registerEventListener(eventName, listener, waitForNext = true)
      
      // Trigger event again
      notifyEventOccurred(eventName)
      
      // Should receive notification
      listener.expectMsg(EventOccurred)
    }
    
    "handle event notification when no listeners registered" in {
      // Should not crash
      noException should be thrownBy {
        notifyEventOccurred("UnregisteredEvent")
      }
      hasFiredEvent("UnregisteredEvent") shouldBe true
    }
  }
  
  "Combined Scenarios" should {
    
    "handle both completion and event listeners simultaneously" in {
      val completionListener = createListenerProbe()
      val eventListener = createListenerProbe()
      val eventName = "TestEvent"
      
      // Register both types
      registerCompletionListener(completionListener)
      registerEventListener(eventName, eventListener)
      
      // Trigger event
      notifyEventOccurred(eventName)
      eventListener.expectMsg(EventOccurred)
      completionListener.expectNoMessage(noMsgTimeout)
      
      // Trigger completion
      notifyCompleted()
      completionListener.expectMsg(Completed)
      eventListener.expectNoMessage(noMsgTimeout)
    }
    
    "handle listener registration after partial completion" in {
      val listener1 = createListenerProbe()
      val listener2 = createListenerProbe()
      val eventName = "TestEvent"
      
      // Fire event
      notifyEventOccurred(eventName)
      
      // Register listener1 after event (should get immediate notification)
      registerEventListener(eventName, listener1, waitForNext = false)
      listener1.expectMsg(EventOccurred)
      
      // Register listener2 for completion (should wait)
      registerCompletionListener(listener2)
      listener2.expectNoMessage(noMsgTimeout)
      
      // Complete
      notifyCompleted()
      listener2.expectMsg(Completed)
    }
  }
  
  "Edge Cases" should {
    
    "handle rapid listener registration" in {
      val listeners = (1 to 10).map(_ => createListenerProbe()).toList
      val eventName = "TestEvent"
      
      // Register many listeners rapidly
      listeners.foreach { listener =>
        registerEventListener(eventName, listener)
      }
      
      // Trigger event
      notifyEventOccurred(eventName)
      
      // All should receive notification
      listeners.foreach { listener =>
        listener.expectMsg(EventOccurred)
      }
    }
    
    "handle rapid event firing" in {
      val listener = createListenerProbe()
      val events = (1 to 5).map(i => s"Event$i").toList
      
      // Register listeners for all events
      events.foreach { eventName =>
        registerEventListener(eventName, listener)
      }
      
      // Fire all events rapidly
      events.foreach(notifyEventOccurred)
      
      // Should receive all notifications
      (1 to 5).foreach { _ =>
        listener.expectMsg(EventOccurred)
      }
    }
    
    "handle same listener registered for multiple events" in {
      val listener = createListenerProbe()
      
      // Register same listener for multiple events
      registerEventListener("Event1", listener)
      registerEventListener("Event2", listener)
      registerEventListener("Event3", listener)
      
      // Fire all events
      notifyEventOccurred("Event1")
      notifyEventOccurred("Event2")
      notifyEventOccurred("Event3")
      
      // Should receive 3 notifications (one per event)
      listener.expectMsg(EventOccurred)
      listener.expectMsg(EventOccurred)
      listener.expectMsg(EventOccurred)
    }
  }
}
