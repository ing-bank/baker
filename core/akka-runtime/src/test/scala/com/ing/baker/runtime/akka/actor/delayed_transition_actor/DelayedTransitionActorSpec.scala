package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import akka.actor.ActorSystem
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol.{FireDelayedTransition, ScheduleDelayedTransition, StartTimer}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexSpec
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.TransitionDelayed
import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.concurrent.Eventually
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatestplus.mockito.MockitoSugar

import java.util.UUID
import scala.concurrent.duration.FiniteDuration

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

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor))

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

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor))

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

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor))

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

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor),
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

      val delayedTransitionActor = system.actorOf(DelayedTransitionActor.props(index.testActor))

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
  }
}
