package com.ing.baker.runtime.actor

import java.util.UUID

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.testkit.{ImplicitSender, TestDuration, TestKit, TestProbe}
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.petrinet.dsl.colored.Place
import com.ing.baker.runtime.actor.PetriNetInstanceProtocol._
import com.ing.baker.runtime.actor.ProcessIndex.ReceivePeriodExpired
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Matchers._
import org.mockito.Mockito
import org.mockito.Mockito.verify
import org.scalatest.concurrent.Eventually
import org.scalatest.mockito.MockitoSugar
import org.scalatest.time.Span
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.duration.{Duration, _}

object ProcessIndexSpec {
  val config: Config = ConfigFactory.parseString(
    """
      |akka.persistence.journal.plugin = "inmemory-journal"
      |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |akka.test.timefactor = 3.0
    """.stripMargin)
}

//noinspection TypeAnnotation
class ProcessIndexSpec extends TestKit(ActorSystem("ProcessIndexSpec", ProcessIndexSpec.config))
  with ImplicitSender
  with WordSpecLike
  with Matchers
  with BeforeAndAfterAll
  with BeforeAndAfter
  with MockitoSugar
  with Eventually {

  val recipeMetadataMock = mock[RecipeMetadata]

  val noMsgExpectTimeout: FiniteDuration = 100.milliseconds

  val otherMsg = mock[PetriNetInstanceProtocol.Command]

  before {
    Mockito.reset(recipeMetadataMock, otherMsg)
  }

  override def afterAll {
    TestKit.shutdownActorSystem(system)
  }

  "ProcessIndex" should {

    "create the PetriNetInstance actor when Initialize message is received" in {
      val initializeCmd = Initialize(Marking.empty[Place])
      val processId = UUID.randomUUID().toString

      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref)

      actorIndex ! BakerActorMessage(processId, initializeCmd)

      petriNetActorProbe.expectMsg(initializeCmd)
    }

    "not create the PetriNetInstance actor if already created" in {
      val initializeMsg = Initialize(Marking.empty[Place])
      val processId = UUID.randomUUID().toString

      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref)

      actorIndex ! BakerActorMessage(processId, initializeMsg)
      actorIndex ! BakerActorMessage(processId, initializeMsg)

      petriNetActorProbe.expectMsg(initializeMsg)
      petriNetActorProbe.expectNoMsg(noMsgExpectTimeout)
      expectMsg(AlreadyInitialized)
    }

    "forward messages to the PetriNetInstance actor" in {
      val initializeMsg = Initialize(Marking.empty[Place])
      val processId = UUID.randomUUID().toString

      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref)

      actorIndex ! BakerActorMessage(processId, initializeMsg)
      actorIndex ! BakerActorMessage(processId, otherMsg)

      petriNetActorProbe.expectMsg(initializeMsg)
      petriNetActorProbe.expectMsg(otherMsg)
    }

    "notify ProcessMetadata when a PetriNetInstance actor is created" in {
      val initializeMsg = Initialize(Marking.empty[Place])
      val processId = UUID.randomUUID().toString

      val actorIndex = createActorIndex(TestProbe().ref)

      actorIndex ! BakerActorMessage(processId, initializeMsg)

      val timeout = Span.convertDurationToSpan(500.milliseconds.dilated)
      val interval = Span.convertDurationToSpan(50.milliseconds.dilated)
      implicit val patienceConfig = PatienceConfig(timeout, interval)
      eventually {
        verify(recipeMetadataMock).add(any[ProcessMetadata])
      }
    }

    "delete a process if a retention period is defined" in {

      val retentionPeriod = 500 milliseconds
      val cleanupInterval = 50 milliseconds

      val processProbe = TestProbe()

      val actorIndex = createActorIndex(processProbe.ref,
        retentionPeriod = retentionPeriod,
        cleanupInterval = cleanupInterval)

      val processId = UUID.randomUUID().toString

      val initializeCmd = Initialize(Marking.empty[Place])
      actorIndex ! BakerActorMessage(processId, initializeCmd )
      processProbe.expectMsg(initializeCmd)

      processProbe.expectMsg(Stop(delete = true))
    }

    "not forward messages to uninitialized actors" in {
      val processId = UUID.randomUUID().toString

      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref)

      actorIndex ! BakerActorMessage(processId, otherMsg)

      petriNetActorProbe.expectNoMsg(noMsgExpectTimeout)
      expectMsg(Uninitialized(processId.toString))
    }

    "reply with a EventReceivePeriodExpired message when attempting to fire an event after expiration period" in {

      val receivePeriodTimeout = 500 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val actorIndex = createActorIndex(petriNetActorProbe.ref, receivePeriod = receivePeriodTimeout)

      val processId = UUID.randomUUID().toString

      val initializeCmd = Initialize(Marking.empty[Place])

      actorIndex ! BakerActorMessage(processId, initializeCmd)
      petriNetActorProbe.expectMsg(initializeCmd)

      val fireTransitionCmd = FireTransition(0L, null, None)
      val replyMsg = "hi"

      actorIndex ! BakerActorMessage(processId, fireTransitionCmd)

      petriNetActorProbe.expectMsg(fireTransitionCmd)
      petriNetActorProbe.reply(replyMsg)

      expectMsg(replyMsg)

      Thread.sleep(receivePeriodTimeout.toMillis)

      actorIndex ! BakerActorMessage(processId, fireTransitionCmd)
      petriNetActorProbe.expectNoMsg(noMsgExpectTimeout)

      expectMsg(ReceivePeriodExpired)
    }
  }

  private def createActorIndex(petriNetActorRef: ActorRef,
                               receivePeriod: Duration = Duration.Undefined,
                               retentionPeriod: Duration = Duration.Undefined,
                               cleanupInterval: FiniteDuration = 50 milliseconds) = {
    val props = Props(new ProcessIndex(Props.empty, recipeMetadataMock, receivePeriod, retentionPeriod, cleanupInterval) {
      override def createProcessActor(id: String) = petriNetActorRef
    })

    system.actorOf(props, s"actorIndex-${UUID.randomUUID().toString}")
  }
}
