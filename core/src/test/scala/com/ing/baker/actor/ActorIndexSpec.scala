package com.ing.baker.actor

import java.util.UUID

import akka.actor.{ActorSystem, Props}
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import com.typesafe.config.ConfigFactory
import io.kagera.akka.actor.PetriNetInstanceProtocol
import io.kagera.akka.actor.PetriNetInstanceProtocol.{AlreadyInitialized, Initialize, Uninitialized}
import io.kagera.api.colored.Marking
import org.mockito
import org.mockito.Mockito.verify
import org.mockito.{ArgumentCaptor, Mockito}
import org.scalatest.concurrent.Eventually
import org.scalatest.mock.MockitoSugar
import org.scalatest.time.{Millis, Seconds, Span}
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll, Matchers, WordSpecLike}

//noinspection TypeAnnotation
class ActorIndexSpec extends TestKit(ActorSystem("ActorIndexSpec", ConfigFactory.parseString(
  """
    |akka.persistence.journal.plugin = "inmemory-journal"
    |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
  """.stripMargin)))
  with ImplicitSender
  with WordSpecLike
  with Matchers
  with BeforeAndAfterAll
  with BeforeAndAfter
  with MockitoSugar
  with Eventually {

  override implicit val patienceConfig = PatienceConfig(Span(3, Seconds), Span(500, Millis))

  var petriNetActorProbe = TestProbe()
  val recipeMetadataMock = mock[RecipeMetadata]

  override def afterAll {
    TestKit.shutdownActorSystem(system)
  }

  before {
    petriNetActorProbe = TestProbe()
    Mockito.reset(recipeMetadataMock)
  }

  "ActorIndex" should {

    "create the PetriNetInstance actor when Initialize message is received" in {
      val initializeMsg = Initialize(Marking.empty)
      val processId = UUID.randomUUID()

      val actorIndex = createActorIndex

      actorIndex ! BakerActorMessage(processId, initializeMsg)
      petriNetActorProbe.expectMsg(initializeMsg)
    }

    "not create the PetriNetInstance actor if already created" in {
      val initializeMsg = Initialize(Marking.empty)
      val processId = UUID.randomUUID()

      val actorIndex = createActorIndex

      actorIndex ! BakerActorMessage(processId, initializeMsg)
      actorIndex ! BakerActorMessage(processId, initializeMsg)

      petriNetActorProbe.expectMsg(initializeMsg)
      petriNetActorProbe.expectNoMsg()
      expectMsg(AlreadyInitialized)
    }

    "forward messages to the PetriNetInstance actor" in {
      val initializeMsg = Initialize(Marking.empty)
      val otherMsg = mock[PetriNetInstanceProtocol.Command]
      val processId = UUID.randomUUID()

      val actorIndex = createActorIndex

      actorIndex ! BakerActorMessage(processId, initializeMsg)
      actorIndex ! BakerActorMessage(processId, otherMsg)

      petriNetActorProbe.expectMsg(initializeMsg)
      petriNetActorProbe.expectMsg(otherMsg)
    }

    "notifies ProcessMetadata when a PetriNetInstance actor is created" in {
      val initializeMsg = Initialize(Marking.empty)
      val processId = UUID.randomUUID()

      val actorIndex = createActorIndex

      val currentTime = System.currentTimeMillis()
      actorIndex ! BakerActorMessage(processId, initializeMsg)

      eventually {
        val captor = ArgumentCaptor.forClass(classOf[Long])
        verify(recipeMetadataMock).addNewProcessMetadata(
          mockito.Matchers.eq(processId.toString),
          captor.capture())

        // check the created time is a sensible long value, not anyLong,
        // i.e. newer than the time BakerActorMessage is sent
        captor.getValue should be > currentTime
      }

    }

    "not forward messages to uninitialized actors" in {
      val processId = UUID.randomUUID()
      val otherMsg = mock[PetriNetInstanceProtocol.Command]

      val actorIndex = createActorIndex

      actorIndex ! BakerActorMessage(processId, otherMsg)
      petriNetActorProbe.expectNoMsg()
      expectMsg(Uninitialized(processId.toString))
    }
  }

  private def createActorIndex = {
    system.actorOf(Props(new ActorIndex(Props.empty, recipeMetadataMock) {
      override private[actor] def createChildPetriNetActor(id: String) = {
        petriNetActorProbe.ref
      }
    }))
  }
}
