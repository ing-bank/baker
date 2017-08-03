package com.ing.baker.runtime.actor

import java.util.UUID

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol._
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.petrinet.dsl.colored.Place
import com.ing.baker.runtime.actor.ProcessIndex.ReceivePeriodExpired
import com.typesafe.config.ConfigFactory
import org.mockito
import org.mockito.Mockito
import org.mockito.Mockito.verify
import org.scalatest.concurrent.Eventually
import org.scalatest.mockito.MockitoSugar
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.duration.{Duration, _}

object ProcessIndexSpec {
  val config =
    """
      |akka.persistence.journal.plugin = "inmemory-journal"
      |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |akka.test.timefactor = 3.0
    """.stripMargin
}

//noinspection TypeAnnotation
class ProcessIndexSpec extends TestKit(ActorSystem("ProcessIndexSpec", ConfigFactory.parseString(ProcessIndexSpec.config)))
    with ImplicitSender
    with WordSpecLike
    with Matchers
    with BeforeAndAfterAll
    with BeforeAndAfter
    with MockitoSugar
    with Eventually {

  val recipeMetadataMock = mock[RecipeMetadata]

  val noMsgExpectTimeout: FiniteDuration = 100 milliseconds

  before {
    Mockito.reset(recipeMetadataMock)
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
      val otherMsg = mock[PetriNetInstanceProtocol.Command]
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

      implicit val patienceConfig = PatienceConfig()
      eventually {
        verify(recipeMetadataMock)
          .addNewProcessMetadata(
            mockito.Matchers.eq(processId.toString),
            mockito.Matchers.anyLong())
      }
    }

    "not forward messages to uninitialized actors" in {
      val processId = UUID.randomUUID().toString
      val otherMsg = mock[PetriNetInstanceProtocol.Command]

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

  private def createActorIndex(petriNetActorRef: ActorRef, receivePeriod: Duration = Duration.Undefined) = {
    system.actorOf(Props(new ProcessIndex(Props.empty, recipeMetadataMock, receivePeriod) {
      override private[actor] def createChildPetriNetActor(id: String) = {
        petriNetActorRef
      }
    }), s"actorIndex-${UUID.randomUUID().toString}")
  }
}
