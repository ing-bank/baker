package com.ing.baker.runtime.actor.process_instance

import java.util.UUID
import java.util.concurrent.TimeUnit

import akka.actor.{ActorRef, ActorSystem, PoisonPill, Terminated}
import akka.testkit.TestDuration
import akka.util.Timeout
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.dsl.colored._
import com.ing.baker.petrinet.runtime.ExceptionStrategy.{BlockTransition, Fatal, RetryWithDelay}
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler
import com.ing.baker.runtime.actor.AkkaTestBase
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
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

sealed trait Event
case class Added(n: Int) extends Event
case class Removed(n: Int) extends Event

trait TestSequenceNet extends SequenceNet[Set[Int], Event] {

  override val eventSourceFunction: Set[Int] ⇒ Event ⇒ Set[Int] = set ⇒ {
    case Added(c)   ⇒ set + c
    case Removed(c) ⇒ set - c
  }
}

class ProcessInstanceSpec extends AkkaTestBase with ScalaFutures with MockitoSugar {

  def dilatedMillis(millis: Long)(implicit system: ActorSystem): Long = FiniteDuration(millis, TimeUnit.MILLISECONDS).dilated.toMillis

  def syncKillActorWithPoisonPill(actor: ActorRef): Unit = {
    watch(actor)
    actor ! PoisonPill
    expectMsgClass(classOf[Terminated])
    Thread.sleep(dilatedMillis(100))
  }

  "A persistent petri net actor" should {

    "Respond with an Initialized response after processing an Initialize command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition()(_ ⇒ Added(2))
      )

      val initialState = Set(1, 2, 3)

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), initialState)
      expectMsg(Initialized(marshal[Place](initialMarking), initialState))
    }

    "Respond with an AlreadyInitialized response after processing an Initialize command for the second time" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition()(_ ⇒ Added(2))
      )

      val initialState = Set(1, 2, 3)

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal[Place](initialMarking), initialState)
      actor ! Initialize(marshal[Place](initialMarking), initialState)
      expectMsg(Initialized(marshal[Place](initialMarking), initialState))
      expectMsg(AlreadyInitialized)
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
      expectMsgClass(classOf[Terminated])
    }

    "After being initialized respond with an InstanceState message on receiving a GetState command" in new TestSequenceNet {

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

    "Respond with a AlreadyReceived message if the given corellation id was received earlier" in new TestSequenceNet {

      val testCorrelationId = "abc"

      override val sequence = Seq(
        transition()(_ ⇒ Added(1))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      // initialize the petri net with 2 tokens in the first place
      actor ! Initialize(marshal[Place](Marking(place(1) -> 2)), Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null, correlationId = Some(testCorrelationId))

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) ⇒ }

      actor ! FireTransition(transitionId = 1, input = null, correlationId = Some(testCorrelationId))

      expectMsg(AlreadyReceived(testCorrelationId))
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

      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, _) ⇒ }

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

      val retryHandler: TransitionExceptionHandler[Place] = {
        case (_, n, _) if n < 3 ⇒ RetryWithDelay(dilatedMillis(10 * Math.pow(2, n).toLong))
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

      val delay1: Long = dilatedMillis(20)
      val delay2: Long = dilatedMillis(40)

      // expect 3 failure messages
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, RetryWithDelay(delay1)) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, RetryWithDelay(delay2)) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, Fatal) ⇒ }

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
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) ⇒ }

      // since t2 fires automatically we also expect the next marking: p3 -> 1
      expectMsgPF() { case TransitionFired(_, 2, _, _, _, _, _) ⇒ }

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

      val Delay: Long = dilatedMillis(500)
      val retryHandler: TransitionExceptionHandler[Place] = {
        case (e, n, _) ⇒ RetryWithDelay(Delay)
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

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 2, _, _, _, _, RetryWithDelay(Delay)) ⇒ }

      // verify that the mock function was called
      verify(mockFunction).apply(any[Set[Int]])

      // kill the actor
      actor ! Stop(delete = false)
      syncKillActorWithPoisonPill(actor)

      // reset the mock
      reset(mockFunction)
      when(mockFunction.apply(any[Set[Int]])).thenReturn(Added(1))

      // create a new actor with the same persistent identifier
      val newActor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      // TODO find a way to prevent this sleep, perhaps listen on the event bus?
      Thread.sleep(dilatedMillis(1000))

      verify(mockFunction).apply(any[Set[Int]])
    }

    "Block a transition if the exception strategy function throws an exception" in new TestSequenceNet {

      val faultyExceptionHandler: TransitionExceptionHandler[Place] = {
        case (_, _, _) ⇒ throw new IllegalStateException("Boom!")
      }

      override def sequence =
        Seq(
          transition(exceptionHandler = faultyExceptionHandler)(_ ⇒ throw new IllegalArgumentException("Failed!"))
        )

      val actorName = UUID.randomUUID().toString
      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)

      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(1, ())

      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, BlockTransition) ⇒ }
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
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) ⇒ }
      expectMsgPF() { case TransitionFailed(_, 2, _, _, _, _, BlockTransition) ⇒ }

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

      val InitialDelay: Long = dilatedMillis(50)
      val retryHandler: TransitionExceptionHandler[Place] = {
        case (e, n, _) ⇒ RetryWithDelay(InitialDelay)
      }

      val mockFunction = mock[Set[Int] ⇒ Event]

      override val sequence = Seq(
        transition(automated = true, exceptionHandler = retryHandler)(mockFunction)
      )

      val mockPromise = Promise[Boolean]

      when(mockFunction.apply(any[Set[Int]])).thenAnswer(new Answer[Event] {
        override def answer(invocationOnMock: InvocationOnMock): Event = {
          mockPromise.complete(Success(true)) // FIXME TRAVIS: sometimes we have PromiseAlreadyCompleted exception here
          throw new RuntimeException("failure")
        }
      })

      val actorName = UUID.randomUUID().toString

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(marshal[Place](initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, RetryWithDelay(InitialDelay)) ⇒ }

      whenReady(mockPromise.future) { _ ⇒

        verify(mockFunction).apply(any[Set[Int]]) // FIXME TRAVIS: sometimes executes 2 times

        // kill the actor
        actor ! Stop(delete = false)
        syncKillActorWithPoisonPill(actor)

        Thread.sleep(dilatedMillis(100))

        reset(mockFunction)

        verifyZeroInteractions(mockFunction)
      }
    }

    "When Idle terminate after some time if an idle TTL has been specified" in new TestSequenceNet {

      val ttl = FiniteDuration(500, MILLISECONDS).dilated

      val customSettings = instanceSettings.copy(idleTTL = Some(ttl))

      override val sequence = Seq(
        transition(automated = false)(_ ⇒ Added(1)),
        transition(automated = false)(_ ⇒ Added(2))
      )

      val petriNetActor = createPetriNetActor(coloredProps(petriNet, runtime, customSettings), UUID.randomUUID().toString)
      watch(petriNetActor)

      implicit val timeout = Timeout(dilatedMillis(2000), MILLISECONDS)

      petriNetActor ! Initialize(marshal[Place](initialMarking), ())
      expectMsgClass(classOf[Initialized])

      expectMsgClass(classOf[Terminated])
    }

    "fire automated transitions in parallel when possible" in new StateTransitionNet[Unit, Unit] {

      override val eventSourceFunction: Unit ⇒ Unit ⇒ Unit = s ⇒ e ⇒ s

      val p1 = Place[Unit](id = 1)
      val p2 = Place[Unit](id = 2)

      val t1 = nullTransition[Unit](id = 1, automated = false)
      val t2 = stateTransition(id = 2, automated = true)(_ ⇒ Thread.sleep(dilatedMillis(500)))
      val t3 = stateTransition(id = 3, automated = true)(_ ⇒ Thread.sleep(dilatedMillis(500)))

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

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) ⇒ }

      import org.scalatest.concurrent.Timeouts._

      failAfter(Span(dilatedMillis(1000), Milliseconds)) {

        // expect that the two subsequent transitions are fired automatically and in parallel (in any order)
        expectMsgInAnyOrderPF(
          { case TransitionFired(_, 2, _, _, _, _, _) ⇒ },
          { case TransitionFired(_, 3, _, _, _, _, _) ⇒ }
        )
      }
    }
  }
}
