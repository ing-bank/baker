package com.ing.baker.petrinet.akka

import java.util.UUID

import akka.actor.{ActorRef, PoisonPill, SupervisorStrategy, Terminated}
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.petrinet.akka.AkkaTestBase.GetChild
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol._
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.dsl.colored._
import com.ing.baker.petrinet.runtime.ExceptionStrategy.{BlockTransition, Fatal, RetryWithDelay}
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock
import org.mockito.stubbing.Answer
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.mockito.MockitoSugar
import org.scalatest.time.{Milliseconds, Span}

import scala.concurrent.Promise
import scala.concurrent.duration._
import scala.util.Success

class PetriNetInstanceSpec extends AkkaTestBase with ScalaFutures with MockitoSugar {

  def syncKillActorWithPoisonPill(actor: ActorRef): Unit = {
    watch(actor)
    actor ! PoisonPill
    expectMsgClass(classOf[Terminated])
    Thread.sleep(100)
  }

  "A persistent petri net actor" should {

    "Respond with an Initialized response after processing an Initialized command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition()(_ ⇒ Added(2))
      )

      val initialState = Set(1, 2, 3)

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), initialState)
      expectMsg(Initialized(marshal[Place](initialMarking), initialState))
    }

    "Before being initialized respond with an Uninitialized message and terminate on receiving a GetState command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition()(_ ⇒ Added(2))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      watch(actor)
      actor ! GetState
      expectMsgClass(classOf[Uninitialized])
    }

    "Afer being initialized respond with an InstanceState message on receiving a GetState command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition()(_ ⇒ Added(2))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)
      val initialState = Set(1, 2, 3)
      val initialMarkingData = marshal[Place](initialMarking)

      actor ! Initialize(initialMarkingData, initialState)
      expectMsgClass(classOf[Initialized])

      actor ! GetState
      expectMsgPF() { case InstanceState(1, `initialMarkingData`, `initialState`, _) ⇒ }
    }

    "Respond with a TransitionFailed message if a transition failed to fire" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ throw new RuntimeException("t1 failed!")),
        transition()(_ ⇒ throw new RuntimeException("t2 failed!"))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(1, ())

      expectMsgClass(classOf[TransitionFailed])
    }

    "Respond with a TransitionNotEnabled message if a transition is not enabled because of a previous failure" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ throw new RuntimeException("t1 failed!")),
        transition()(_ ⇒ Added(2))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(1, ())

      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _) ⇒ }

      actor ! FireTransition(1, ())

      // expect a failure message
      expectMsgPF() { case TransitionNotEnabled(1, msg) ⇒ }
    }

    "Respond with a TransitionNotEnabled message if a transition is not enabled because of not enough consumable tokens" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition()(_ ⇒ Added(2))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      // attempt to fire the second transition
      actor ! FireTransition(2, ())

      // expect a failure message
      expectMsgPF() { case TransitionNotEnabled(2, _) ⇒ }
    }

    "Retry to execute a transition with a delay when the exception strategy indicates so" in new TestSequenceNet {

      val retryHandler: TransitionExceptionHandler = {
        case (e, n) if n < 3 ⇒ RetryWithDelay((10 * Math.pow(2, n)).toLong)
        case _               ⇒ Fatal
      }

      override val sequence = Seq(
        transition(exceptionHandler = retryHandler) { _ ⇒ throw new RuntimeException("t1 failed") },
        transition() { _ ⇒ Added(2) }
      )

      val id = UUID.randomUUID()

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(1, ())

      // expect 3 failure messages
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, RetryWithDelay(20)) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, RetryWithDelay(40)) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, Fatal) ⇒ }

      // attempt to fire t1 explicitly
      actor ! FireTransition(1, ())

      // expect the transition to be not enabled
      val msg = expectMsgClass(classOf[TransitionNotEnabled])
    }

    "Be able to restore it's state from persistent storage after termination" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition(automated = true)(_ ⇒ Added(2))
      )

      val actorName = UUID.randomUUID().toString

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      // fire the first transition (t1) manually
      actor ! FireTransition(1, ())

      // expect the next marking: p2 -> 1
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _) ⇒ }

      // since t2 fires automatically we also expect the next marking: p3 -> 1
      expectMsgPF() { case TransitionFired(_, 2, _, _, _, _) ⇒ }

      // validate the final state
      val expectedFinalState = InstanceState(3, marshal[Place](Marking(place(3) -> 1)), Set(1, 2), Map.empty)
      actor ! GetState
      expectMsg(expectedFinalState)

      // terminate the actor
      syncKillActorWithPoisonPill(actor)

      // create a new actor with the same persistent identifier
      val newActor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      newActor ! GetState

      // assert that the actor is the same as before termination
      expectMsg(expectedFinalState)
    }

    "Re-fire a failed transition with 'Retry' strategy after being restored from persistent storage" in new TestSequenceNet {
      val retryHandler: TransitionExceptionHandler = {
        case (e, n) ⇒ RetryWithDelay(500)
      }
      val mockFunction = mock[Set[Int] ⇒ Event]

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition(automated = true, exceptionHandler = retryHandler)(mockFunction)
      )

      when(mockFunction.apply(any[Set[Int]])).thenThrow(new RuntimeException("t2 failed"))

      val actorName = UUID.randomUUID().toString
      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(1, ())

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 2, _, _, _, RetryWithDelay(500)) ⇒ }

      // verify that the mock function was called
      verify(mockFunction).apply(any[Set[Int]])

      // kill the actor
      actor ! SupervisorStrategy.Stop
      syncKillActorWithPoisonPill(actor)

      // reset the mock
      reset(mockFunction)
      when(mockFunction.apply(any[Set[Int]])).thenReturn(Added(1))

      // create a new actor with the same persistent identifier
      val newActor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      // TODO find a way to prevent this sleep, perhaps listen on the event bus?
      Thread.sleep(1000)

      verify(mockFunction).apply(any[Set[Int]])
    }

    "Not re-fire a failed transition with 'Blocked' strategy after being restored from persistent storage" in new TestSequenceNet {

      // setup a failing mock function
      val mockT2 = mock[Set[Int] ⇒ Event]
      when(mockT2.apply(any[Set[Int]])).thenThrow(new RuntimeException("t2 mock failed"))

      override val sequence = Seq(
        transition(automated = true)(_ ⇒ Added(1)),
        transition(automated = true)(mockT2)
      )

      val processId = UUID.randomUUID().toString

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime, processId)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      // expect the next marking: p2 -> 1
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 2, _, _, _, BlockTransition) ⇒ }

      verify(mockT2).apply(any[Set[Int]])

      // terminate the actor
      syncKillActorWithPoisonPill(actor)

      reset(mockT2)

      // create a new actor with the same persistent identifier
      val newActor = createPetriNetActor[Set[Int], Event](petriNet, runtime, processId)

      newActor ! GetState

      // assert that the actor is the same as before termination
      expectMsgPF() { case InstanceState(2, marking, _, jobs) ⇒ }

      verifyZeroInteractions(mockT2)
    }

    "Not execute a transition with scheduled retry after being stopped" in new TestSequenceNet {

      val retryHandler: TransitionExceptionHandler = {
        case (e, n) ⇒ RetryWithDelay(50)
      }

      val mockFunction = mock[Set[Int] ⇒ Event]

      override val sequence = Seq(
        transition(automated = true, exceptionHandler = retryHandler)(mockFunction)
      )

      val mockPromise = Promise[Boolean]

      when(mockFunction.apply(any[Set[Int]])).thenAnswer(new Answer[Event] {
        override def answer(invocationOnMock: InvocationOnMock): Event = {
          mockPromise.complete(Success(true))
          throw new RuntimeException("failure")
        }
      })

      val actorName = UUID.randomUUID().toString

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, RetryWithDelay(50)) ⇒ }

      whenReady(mockPromise.future) { _ ⇒

        verify(mockFunction).apply(any[Set[Int]])

        // kill the actor
        actor ! SupervisorStrategy.Stop
        syncKillActorWithPoisonPill(actor)

        Thread.sleep(100)

        reset(mockFunction)

        verifyZeroInteractions(mockFunction)
      }
    }

    "When Idle terminate after some time if an idle TTL has been specified" in new TestSequenceNet {

      val ttl = 500 milliseconds

      val customSettings = instanceSettings.copy(idleTTL = Some(ttl))

      override val sequence = Seq(
        transition(automated = false)(_ ⇒ Added(1)),
        transition(automated = false)(_ ⇒ Added(2))
      )

      val petriNetActor = createPetriNetActor(coloredProps(petriNet, runtime, customSettings), UUID.randomUUID().toString)

      implicit val timeout = Timeout(2 seconds)
      whenReady((petriNetActor ? GetChild).mapTo[ActorRef]) {
        child ⇒
          {
            petriNetActor ! Initialize(marshal[Place](initialMarking), ())
            expectMsgClass(classOf[Initialized])

            watch(child)
            expectMsgClass(classOf[Terminated])
          }
      }
    }

    "fire automated transitions in parallel when possible" in new StateTransitionNet[Unit, Unit] {

      override val eventSourceFunction: Unit ⇒ Unit ⇒ Unit = s ⇒ e ⇒ s

      val p1 = Place[Unit](id = 1)
      val p2 = Place[Unit](id = 2)

      val t1 = nullTransition[Unit](id = 1, automated = false)
      val t2 = stateTransition(id = 2, automated = true)(_ ⇒ Thread.sleep(500))
      val t3 = stateTransition(id = 3, automated = true)(_ ⇒ Thread.sleep(500))

      val petriNet = createPetriNet[Unit](
        t1 ~> p1,
        t1 ~> p2,
        p1 ~> t2,
        p2 ~> t3
      )

      // creates a petri net actor with initial marking: p1 -> 1
      val initialMarking = Marking.empty[Place]

      val actor = createPetriNetActor[Unit, Unit](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), ())
      expectMsgClass(classOf[Initialized])

      // fire the first transition manually
      actor ! FireTransition(1, ())

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _) ⇒ }

      import org.scalatest.concurrent.Timeouts._

      failAfter(Span(1000, Milliseconds)) {

        // expect that the two subsequent transitions are fired automatically and in parallel (in any order)
        expectMsgInAnyOrderPF(
          { case TransitionFired(_, 2, _, _, _, _) ⇒ },
          { case TransitionFired(_, 3, _, _, _, _) ⇒ }
        )
      }
    }
  }
}
