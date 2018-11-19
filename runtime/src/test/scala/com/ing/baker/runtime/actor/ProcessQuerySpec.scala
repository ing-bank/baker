package com.ing.baker.runtime.actor

import java.util.UUID

import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.stream.ActorMaterializer
import akka.stream.testkit.scaladsl.TestSink
import akka.testkit.TestProbe
import akka.util.Timeout
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceEventSourcing._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceSpec._
import com.ing.baker.runtime.actor.process_instance.dsl._
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import org.scalatest.BeforeAndAfterEach
import org.scalatest.Matchers._

import scala.collection.immutable._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

class ProcessQuerySpec extends AkkaTestBase("ProcessQuerySpec") with BeforeAndAfterEach {

  implicit val akkaTimout = Timeout(2 seconds)
  val timeOut: Duration = akkaTimout.duration

  implicit def materializer = ActorMaterializer()

  implicit def ec: ExecutionContext = system.dispatcher

  override protected def beforeEach(): Unit = {
    // Clean the journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(system).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

  "The query package" should {

    "return a source of events for a petriNet instance" in new StateTransitionNet[Unit, Unit] {

      override val eventSourceFunction: Unit ⇒ Unit ⇒ Unit = s ⇒ _ ⇒ s

      val readJournal = PersistenceQuery(system).readJournalFor[ReadJournal with CurrentEventsByPersistenceIdQuery]("inmemory-read-journal")

      val p1 = Place(id = 1)
      val p2 = Place(id = 2)
      val p3 = Place(id = 3)
      val t1 = nullTransition(id = 1, automated = true)
      val t2 = nullTransition(id = 2, automated = true)

      val petriNet = createPetriNet(p1 ~> t1, t1 ~> p2, p2 ~> t2, t2 ~> p3)
      val processId = UUID.randomUUID().toString
      val instance = createProcessInstance[Unit, Unit](petriNet, runtime, processId)

      instance ! Initialize(p1.markWithN(1), ())

      expectMsg(Initialized(p1.markWithN(1), ()))
      expectMsgPF(timeOut) { case TransitionFired(_, 1, _, _, _, _, _, _) ⇒ }
      expectMsgPF(timeOut) { case TransitionFired(_, 2, _, _, _, _, _, _) ⇒ }

      ProcessQuery.eventsForInstance[Place, Transition, Unit, Unit](
        "test",
        processId,
        petriNet,
        NoEncryption,
        readJournal,
        t ⇒ eventSourceFunction)
        .map(_._2) // Get the event from the tuple
        .runWith(TestSink.probe)
        .request(3)
        .expectNext(InitializedEvent(marking = p1.markWithN(1).marshall, state = ()))
        .expectNextChainingPF {
          case TransitionFiredEvent(_, 1, _, _, _, consumed, produced, _) ⇒
            consumed shouldBe p1.markWithN(1).marshall
            produced shouldBe p2.markWithN(1).marshall
        }.expectNextChainingPF {
          case TransitionFiredEvent(_, 2, _, _, _, consumed, produced, _) ⇒
            consumed shouldBe p2.markWithN(1).marshall
            produced shouldBe p3.markWithN(1).marshall
        }

    }

    "return all persisted processIds" in new StateTransitionNet[Unit, Unit] {

      override val eventSourceFunction: Unit ⇒ Unit ⇒ Unit = s ⇒ e ⇒ s

      val readJournal = PersistenceQuery(system).readJournalFor[ReadJournal with PersistenceIdsQuery]("inmemory-read-journal")

      // Setup petriNet and instances

      val p1 = Place(id = 1)
      val p2 = Place(id = 2)
      val p3 = Place(id = 3)
      val t1 = nullTransition(id = 1, automated = true)
      val t2 = nullTransition(id = 2, automated = true)
      val petriNet = createPetriNet(p1 ~> t1, t1 ~> p2, p2 ~> t2, t2 ~> p3)

      val processId1 = UUID.randomUUID().toString
      val instance1 = createProcessInstance[Unit, Unit](petriNet, runtime, processId1)

      val processId2 = UUID.randomUUID().toString
      val instance2 = createProcessInstance[Unit, Unit](petriNet, runtime, processId2)

      val processId3 = UUID.randomUUID().toString
      val instance3 = createProcessInstance[Unit, Unit](petriNet, runtime, processId3)

      instance1 ! Initialize(Marking.empty[Place], ())
      instance2 ! Initialize(Marking.empty[Place], ())
      instance3 ! Initialize(Marking.empty[Place], ())

      // Setup is finished here, now continue with assertions

      ProcessQuery.allProcessIds("test", readJournal)
        .runWith(TestSink.probe)
        .request(3)
        .expectNextUnorderedN(Seq(processId1, processId2, processId3))
        .expectNoMessage(1.second)
    }

    "return current persisted processIds, stream stopped in the end" in new StateTransitionNet[Unit, Unit] {

      override val eventSourceFunction: Unit ⇒ Unit ⇒ Unit = s ⇒ e ⇒ s

      val readJournal = PersistenceQuery(system).readJournalFor[ReadJournal with CurrentPersistenceIdsQuery]("inmemory-read-journal")

      // Setup petriNet and instances

      val p1 = Place(id = 1)
      val p2 = Place(id = 2)
      val p3 = Place(id = 3)
      val t1 = nullTransition(id = 1, automated = true)
      val t2 = nullTransition(id = 2, automated = true)
      val petriNet = createPetriNet(p1 ~> t1, t1 ~> p2, p2 ~> t2, t2 ~> p3)

      val processId1 = UUID.randomUUID().toString
      val instance1 = createProcessInstance[Unit, Unit](petriNet, runtime, processId1)

      val processId2 = UUID.randomUUID().toString
      val instance2 = createProcessInstance[Unit, Unit](petriNet, runtime, processId2)

      val processId3 = UUID.randomUUID().toString
      val instance3 = createProcessInstance[Unit, Unit](petriNet, runtime, processId3)

      instance1 ! Initialize(Marking.empty[Place], ())
      instance2 ! Initialize(Marking.empty[Place], ())
      instance3 ! Initialize(Marking.empty[Place], ())

      // Setup is finished here, now continue with assertions

      Thread.sleep(1000) // Wait here because otherwise we get an empty completed stream.

      ProcessQuery.currentProcessIds("test", readJournal)
        .runWith(TestSink.probe)
        .request(3)
        .expectNextUnorderedN(Seq(processId1, processId2, processId3))
        .expectComplete()
    }

  }
}
