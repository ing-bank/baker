package com.ing.baker.runtime.akka.actor.listener_manager

import akka.actor.{ActorSystem, PoisonPill}
import akka.testkit.{TestKit, TestProbe}
import com.ing.baker.runtime.akka.actor.listener_manager.ListenerManagerActor._
import com.typesafe.config.ConfigFactory
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach}

import scala.concurrent.duration._

/**
 * Tests for ListenerManagerActor using the ListenerBehaviorSpec.
 * 
 * This test suite implements the same behavioral tests as ProcessInstanceListenerBehaviorSpec
 * to ensure the extracted ListenerManagerActor has identical behavior to the original
 * ProcessInstance listener management.
 * 
 * All 18 tests from ListenerBehaviorSpec must pass to verify:
 * - Completion listener registration and notification
 * - Event listener registration and notification
 * - Immediate notification when already completed/fired
 * - Multiple listeners
 * - Re-registration after notification
 * - Edge cases
 */
class ListenerManagerActorSpec
  extends TestKit(ActorSystem(
    "ListenerManagerActorSpec",
    ConfigFactory.parseString(
      """
        |akka.persistence.journal.plugin = "akka.persistence.journal.inmem"
        |akka.persistence.snapshot-store.plugin = "akka.persistence.snapshot-store.local"
        |akka.persistence.snapshot-store.local.dir = "target/snapshots"
        |akka.loggers = ["akka.testkit.TestEventListener"]
        |akka.loglevel = "WARNING"
        |""".stripMargin)))
  with ListenerBehaviorSpec
  with BeforeAndAfterAll
  with BeforeAndAfterEach {
  
  private var listenerManager: akka.actor.ActorRef = _
  private var recipeInstanceId: String = _
  
  // Track state for test queries
  private var _completedNotified: Boolean = false
  private var _firedEvents: Set[String] = Set.empty
  
  override def beforeEach(): Unit = {
    super.beforeEach()
    _completedNotified = false
    _firedEvents = Set.empty
    recipeInstanceId = java.util.UUID.randomUUID().toString
    listenerManager = system.actorOf(ListenerManagerActor.props(recipeInstanceId))
    // Give the actor time to initialize
    Thread.sleep(50)
  }
  
  override def afterEach(): Unit = {
    if (listenerManager != null) {
      listenerManager ! PoisonPill
      Thread.sleep(50)
    }
    super.afterEach()
  }
  
  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(system)
    super.afterAll()
  }
  
  // Implement abstract methods from ListenerBehaviorSpec
  
  override def registerCompletionListener(listenerProbe: TestProbe): Unit = {
    listenerManager.tell(RegisterCompletionListener(listenerProbe.ref.path.toSerializationFormat), listenerProbe.ref)
  }
  
  override def registerEventListener(eventName: String, listenerProbe: TestProbe, waitForNext: Boolean): Unit = {
    listenerManager.tell(
      RegisterEventListener(eventName, listenerProbe.ref.path.toSerializationFormat, waitForNext),
      listenerProbe.ref
    )
  }
  
  override def notifyEventOccurred(eventName: String): Unit = {
    _firedEvents = _firedEvents + eventName
    listenerManager ! NotifyEventOccurred(eventName)
    // Give time for the actor to process the message
    Thread.sleep(50)
  }
  
  override def notifyCompleted(): Unit = {
    _completedNotified = true
    listenerManager ! NotifyCompleted
    // Give time for the actor to process the message
    Thread.sleep(50)
  }
  
  override def isCompleted: Boolean = {
    // Query the actor's state (for test purposes, we track this via notifications)
    // In practice, this is checked by whether NotifyCompleted was called
    // For these tests, we'll use a simple flag
    _completedNotified
  }
  
  override def hasFiredEvent(eventName: String): Boolean = {
    // Query the actor's state (for test purposes, we track this via notifications)
    _firedEvents.contains(eventName)
  }
  
  override def createListenerProbe(): TestProbe = {
    TestProbe()
  }
}
