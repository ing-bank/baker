package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import akka.actor.{ActorSystem, Props}
import akka.persistence.{SaveSnapshotSuccess, SnapshotMetadata}
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActor.DelayedTransitionSnapshot
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol.{FireDelayedTransition, FireDelayedTransitionAck, ScheduleDelayedTransition, StartTimer}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.TransitionDelayed
import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.concurrent.Eventually
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

import java.util.UUID

object DelayedTransitionActorSpec {
  val config: Config = ConfigFactory.parseString(
    """
      |akka.actor.allow-java-serialization = off
      |baker.actor.snapshot-interval = 1
      |akka.persistence.journal.plugin = "inmemory-journal"
      |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |akka.test.timefactor = 3.0
  """.stripMargin)
}

class DelayedTransitionActorSpec  extends TestKit(ActorSystem("DelayedTransitionActorSpec", DelayedTransitionActorSpec.config))
  with ImplicitSender
  with AnyWordSpecLike
  with Matchers
  with BeforeAndAfterAll
  with BeforeAndAfter
  with MockitoSugar
  with Eventually {


  "DelayedTransitionActor" should {
    "acknowledge the ScheduleDelayedTransition with a TransitionDelayed" in {
      val index = TestProbe("index-probe")

      val delayedTransitionActor = system.actorOf(
        DelayedTransitionActor.props(index.testActor, null, 1000, 1000))

      val recipeId = UUID.randomUUID().toString
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      val receiver = TestProbe()
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
    }

    "Fire the FireDelayedTransition when the Time is up" in {
      val index = TestProbe("index-probe")

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor, null, 1000, 1000))

      val recipeId = UUID.randomUUID().toString
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      delayedTransitionActor ! StartTimer

      val receiver = TestProbe()
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      Thread.sleep(10)
      index.expectMsg(FireDelayedTransition(recipeId, jobId, transitionId, eventToFire, receiver.testActor))
    }

    "Not fire the FireDelayedTransition when the StartTimer is not given" in {
      val index = TestProbe("index-probe")

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor, null, 1000, 1000))

      val recipeId = UUID.randomUUID().toString
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      val receiver = TestProbe()
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      Thread.sleep(10)
      index.expectNoMessage()
    }

    "Fire old messages after when the StartTimer is not given" in {
      val index = TestProbe("index-probe")

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor, null, 1000, 1000),
        s"DelayedTransitionActor4")

      val recipeId = UUID.randomUUID().toString
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      val receiver = TestProbe()
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      Thread.sleep(10)
      index.expectNoMessage()

      delayedTransitionActor ! StartTimer
      index.expectMsg(FireDelayedTransition(recipeId, jobId, transitionId, eventToFire, receiver.testActor))
    }

    "Not Fire the FireDelayedTransition multiple times if given" in {
      val index = TestProbe("index-probe")

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor, null, 1000, 1000))

      val recipeId = UUID.randomUUID().toString
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      delayedTransitionActor ! StartTimer

      val receiver = TestProbe()
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))

      Thread.sleep(10)
      index.expectMsg(FireDelayedTransition(recipeId, jobId, transitionId, eventToFire, receiver.testActor))
      index.expectNoMessage()
    }

    "Create snapshots and cleanup Snapshots" in {
      val index = TestProbe("index-probe")

      var sequenceCount = 0
      var snapshotCount = 0

      var latestSnapshot: Any = null

      class temp extends DelayedTransitionActor(index.testActor, null, 1, 5) {
        override def saveSnapshot(snapshot: Any): Unit = {
          sequenceCount += 1
          snapshotCount += 1
          latestSnapshot = snapshot
          self.tell(SaveSnapshotSuccess(SnapshotMetadata("persistenceId", sequenceCount)), self)
        }

        override def cleanupSnapshots(persistenceId: String, snapShotsToKeep: Int): Unit = {
          if(snapshotCount > snapShotsToKeep ) snapshotCount = snapShotsToKeep
        }
      }

      val delayedTransitionActor =
        system.actorOf(Props(new temp))

      val recipeId = UUID.randomUUID().toString
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      delayedTransitionActor ! StartTimer

      // Test 1 should create 1 Snapshot after 2 messages (first message snapshot is skipped for first message)
      val receiver = TestProbe()
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      Thread.sleep(10)
      index.expectMsg(FireDelayedTransition(recipeId, jobId, transitionId, eventToFire, receiver.testActor))
      index.expectNoMessage()
      delayedTransitionActor.tell(FireDelayedTransitionAck(recipeId, jobId), receiver.testActor)
      Thread.sleep(10)
      assert(snapshotCount == 1)

      // Test 2 should create 3 Snapshot after 4 messages
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      Thread.sleep(10)
      index.expectMsg(FireDelayedTransition(recipeId, jobId, transitionId, eventToFire, receiver.testActor))
      index.expectNoMessage()
      delayedTransitionActor.tell(FireDelayedTransitionAck(recipeId, jobId), receiver.testActor)
      Thread.sleep(10)
      assert(snapshotCount == 3)

      // Test 2 should create 6 Snapshot after 7 messages but cleanup after 5
      delayedTransitionActor.tell(ScheduleDelayedTransition(recipeId, 0, jobId, transitionId, null, eventToFire, receiver.testActor), receiver.testActor)
      receiver.expectMsg(TransitionDelayed(jobId, transitionId, null))
      Thread.sleep(10)
      index.expectMsg(FireDelayedTransition(recipeId, jobId, transitionId, eventToFire, receiver.testActor))
      index.expectNoMessage()
      delayedTransitionActor.tell(FireDelayedTransitionAck(recipeId, jobId), receiver.testActor)
      Thread.sleep(10)
      assert(snapshotCount == 5)

      // Validate that the latest snapshot only has the final open request left over
      val finalSnapshot = latestSnapshot.asInstanceOf[DelayedTransitionSnapshot].waitingTransitions
      assert(finalSnapshot.size == 1)
    }
  }
}
