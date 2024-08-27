package com.ing.baker.runtime.akka.actor.process_instance

import akka.actor.{ActorRef, ActorSystem, PoisonPill, Props, Terminated}
import akka.event.DiagnosticLoggingAdapter
import akka.testkit.{TestDuration, TestProbe}
import akka.util.Timeout
import com.ing.baker.il.{CompiledRecipe, EventDescriptor, IngredientDescriptor}
import com.ing.baker.il.failurestrategy.{BlockInteraction, FireEventAfterFailure, InteractionFailureStrategy, RetryWithIncrementalBackoff}
import com.ing.baker.il.petrinet.{InteractionTransition, Place}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.AkkaTestBase
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventRejection
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventRejection.FiringLimitMet
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstance.Settings
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.BlockTransition
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceSpec._
import com.ing.baker.runtime.akka.actor.process_instance.dsl.TestUtils.{PlaceMethods, place}
import com.ing.baker.runtime.akka.actor.process_instance.dsl._
import com.ing.baker.runtime.akka.actor.process_instance.internal.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.akka.actor.process_instance.{ProcessInstanceProtocol => protocol}
import com.ing.baker.runtime.akka.internal.FatalInteractionException
import com.ing.baker.runtime.akka.namedCachedThreadPool
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import com.ing.baker.runtime.serialization.Encryption.NoEncryption
import com.ing.baker.types
import com.ing.baker.types.{Converters, Value}
import org.mockito.ArgumentMatchers.any
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock
import org.mockito.stubbing.Answer
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.matchers.should.Matchers
import org.scalatest.time.{Milliseconds, Span}
import org.scalatestplus.mockito.MockitoSugar

import java.time.Duration
import java.util.UUID
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.immutable.Seq
import scala.concurrent.Promise
import scala.concurrent.duration.Duration.Zero
import scala.concurrent.duration._
import scala.util.Success


sealed trait Event

case class Added(n: Int) extends Event

case class Removed(n: Int) extends Event

trait TestSequenceNet extends SequenceNet[Set[Int], Event] {

  override val eventSourceFunction: Set[Int] => Event => Set[Int] = set => {
    case Added(c)   => set + c
    case Removed(c) => set - c
  }
}

object ProcessInstanceSpec {

  val testExecutionContext = namedCachedThreadPool(s"Baker.CachedThreadPool")

  val instanceSettings = Settings(
    executionContext = testExecutionContext,
    idleTTL = None,
    encryption = NoEncryption,
    Seq.empty,
    Seq.empty
  )

  def processInstanceProps[S, E](
                                  topology: PetriNet,
                                  runtime: ProcessInstanceRuntime[S, E],
                                  settings: Settings,
                                  delayedTransitionActor: ActorRef): Props = {
    Props(new ProcessInstance[S, E](
      "test",
      CompiledRecipe("name", UUID.randomUUID().toString, topology, Marking.empty, Seq.empty, Option.empty, Option.empty),
      settings,
      runtime,
      delayedTransitionActor)
    )
  }

  def createPetriNetActor(props: Props, name: String)(implicit system: ActorSystem): ActorRef = {
    system.actorOf(props, name)
  }

  def createProcessInstance[S, E](petriNet: PetriNet,
                                  runtime: ProcessInstanceRuntime[S, E],
                                  recipeInstanceId: String = UUID.randomUUID().toString,
                                  delayedTransitionActor: ActorRef = null)(implicit system: ActorSystem): ActorRef = {

    createPetriNetActor(processInstanceProps(petriNet, runtime, instanceSettings, delayedTransitionActor), recipeInstanceId)
  }
}

class ProcessInstanceSpec extends AkkaTestBase("ProcessInstanceSpec") with ScalaFutures with MockitoSugar with Matchers {

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
        transition()(_ => Added(1)),
        transition()(_ => Added(2))
      )

      val initialState = Set(1, 2, 3)

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, initialState)
      expectMsg(Initialized(initialMarking, initialState))
    }

    "Respond with an AlreadyInitialized response after processing an Initialize command for the second time" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => Added(1)),
        transition()(_ => Added(2))
      )

      val initialState = Set(1, 2, 3)

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, initialState)
      actor ! Initialize(initialMarking, initialState)
      expectMsg(Initialized(initialMarking, initialState))
      expectMsgClass(classOf[AlreadyInitialized])
    }

    "Before being initialized respond with an Uninitialized message and terminate on receiving a GetState command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => Added(1)),
        transition()(_ => Added(2))
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      watch(actor)
      actor ! GetState
      expectMsgClass(classOf[Uninitialized])
    }

    "After being initialized respond with an InstanceState message on receiving a GetState command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => Added(1)),
        transition()(_ => Added(2))
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)
      val initialState = Set(1, 2, 3)

      actor ! Initialize(initialMarking, initialState)
      expectMsgClass(classOf[Initialized])

      actor ! GetState
      expectMsgPF() { case InstanceState(1, initialMarkingData, `initialState`, _) if initialMarking.marshall == initialMarkingData => }
    }

    "Respond with a TransitionFailed message if a transition failed to fire" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => throw new RuntimeException("t1 failed!")),
        transition()(_ => throw new RuntimeException("t2 failed!"))
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgClass(classOf[TransitionFailed])
    }

    "Be able to retry a failed (blocked) transition when requested" in new TestSequenceNet {

      val counter = new AtomicInteger(0)

      override val sequence = Seq(
        transition() { _ =>
          if (counter.getAndIncrement() == 0)
            throw new RuntimeException("t1 failed!")
          else
            Added(1)
        })

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgClass(classOf[TransitionFailed])

      actor ! GetState

      val state: InstanceState = expectMsgClass(classOf[InstanceState])

      state.jobs.size shouldBe 1

      val (jobId, jobState) = state.jobs.head

      jobState.exceptionState should matchPattern {
        case Some(ExceptionState(_, _, BlockTransition)) =>
      }

      actor ! OverrideExceptionStrategy(jobId, protocol.ExceptionStrategy.RetryWithDelay(0))

      // expect that the failure is resolved
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) => }
    }

    "Be able to resolve a failed (blocked) transition when requested" in new TestSequenceNet {

      override val sequence = Seq(
        transition() { _ => throw new RuntimeException("t1 failed!") })

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgClass(classOf[TransitionFailed])

      actor ! GetState

      val state: InstanceState = expectMsgClass(classOf[InstanceState])

      state.jobs.size shouldBe 1

      val (jobId, jobState) = state.jobs.head

      jobState.exceptionState should matchPattern {
        case Some(ExceptionState(_, _, BlockTransition)) =>
      }

      actor ! OverrideExceptionStrategy(jobId, protocol.ExceptionStrategy.Continue(place(2).markWithN(1).marshall, Added(2)))

      // expect that the failure is resolved
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, Added(2)) => }
    }

    "Be able to block a retrying transition when requested" in new TestSequenceNet {

      val retryHandler: TransitionExceptionHandler[Place] = {
        case (_, n, _) if n < 3 => RetryWithDelay(5000)
        case _                  => internal.ExceptionStrategy.BlockTransition
      }

      override val sequence = Seq(
        transition(exceptionHandler = retryHandler) { _ => throw new RuntimeException("Expected test failure") }
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgClass(classOf[TransitionFailed])

      actor ! GetState

      val state: InstanceState = expectMsgClass(classOf[InstanceState])

      state.jobs.size shouldBe 1

      val (jobId, jobState) = state.jobs.head

      jobState.exceptionState should matchPattern {
        case Some(ExceptionState(_, _, protocol.ExceptionStrategy.RetryWithDelay(5000))) =>
      }

      actor ! OverrideExceptionStrategy(jobId, protocol.ExceptionStrategy.BlockTransition)

      // expect that the failure is resolved
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, protocol.ExceptionStrategy.BlockTransition) => }
    }

    "Respond with a AlreadyReceived rejection message if the given corellation id was received earlier" in new TestSequenceNet {

      val testCorrelationId = "abc"

      override val sequence = Seq(
        transition()(_ => Added(1))
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      // initialize the petri net with 2 tokens in the first place
      val marking: Marking[Place] = place(1).markWithN(2)

      actor ! Initialize(marking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null, correlationId = Some(testCorrelationId))

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) => }

      actor ! FireTransition(transitionId = 1, input = null, correlationId = Some(testCorrelationId))

      expectMsgType[FireSensoryEventRejection.AlreadyReceived]
    }

    "Respond with a FiringLimitMet rejection message if a transition is not enabled because of a previous failure" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => throw new RuntimeException("t1 failed!")),
        transition()(_ => Added(2))
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, _) => }

      actor ! FireTransition(transitionId = 1, ())

      // expect a failure message
      expectMsgType[FireSensoryEventRejection.FiringLimitMet]
    }

    "Respond with a FiringLimitMet message if a transition is not enabled because of not enough consumable tokens" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => Added(1)),
        transition()(_ => Added(2))
      )

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      // attempt to fire the second transition
      actor ! FireTransition(transitionId = 2, input = null)

      // expect a failure message
      expectMsgType[FiringLimitMet]
    }

    "Retry to execute a transition with a delay when the exception strategy indicates so" in new TestSequenceNet {

      val retryHandler: TransitionExceptionHandler[Place] = {
        case (_, n, _) if n < 3 => RetryWithDelay(dilatedMillis(10 * Math.pow(2, n).toLong))
        case _                  => internal.ExceptionStrategy.BlockTransition
      }

      override val sequence = Seq(
        transition(exceptionHandler = retryHandler) { _ => throw new RuntimeException("t1 failed") },
        transition() { _ => Added(2) }
      )

      val id = UUID.randomUUID()

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      val delay1: Long = dilatedMillis(20)
      val delay2: Long = dilatedMillis(40)

      // expect 3 failure messages
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, protocol.ExceptionStrategy.RetryWithDelay(delay1)) => }
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, protocol.ExceptionStrategy.RetryWithDelay(delay2)) => }
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, protocol.ExceptionStrategy.BlockTransition) => }

      // attempt to fire t1 explicitly
      actor ! FireTransition(transitionId = 1, input = null)

      // expect the transition to be not enabled
      expectMsgType[FiringLimitMet]
    }

    "Be able to restore it's state from persistent storage after termination" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ => Added(1)),
        transition(automated = true)(_ => Added(2))
      )

      val actorName = UUID.randomUUID().toString

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      // fire the first transition (t1) manually
      actor ! FireTransition(transitionId = 1, input = null)

      // expect the next marking: p2 -> 1
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) => }

      // since t2 fires automatically we also expect the next marking: p3 -> 1
      expectMsgPF() { case TransitionFired(_, 2, _, _, _, _, _) => }

      // validate the final state
      val endMarking: Marking[Place] = place(3).markWithN(1)
      val expectedFinalState = InstanceState(3, endMarking.marshall, Set(1, 2), Map.empty)
      actor ! GetState
      expectMsg(expectedFinalState)

      // terminate the actor
      syncKillActorWithPoisonPill(actor)

      // create a new actor with the same persistent identifier
      val newActor = createProcessInstance[Set[Int], Event](petriNet, runtime, actorName)

      newActor ! GetState

      // assert that the actor is the same as before termination
      expectMsg(expectedFinalState)
    }

    "Re-fire a failed transition with 'Retry' strategy after being restored from persistent storage" in new TestSequenceNet {

      val Delay: Long = dilatedMillis(500)
      val retryHandler: TransitionExceptionHandler[Place] = {
        case (e, n, _) => RetryWithDelay(Delay)
      }
      val mockFunction = mock[Set[Int] => Event]

      override val sequence = Seq(
        transition()(_ => Added(1)),
        transition(automated = true, exceptionHandler = retryHandler)(mockFunction)
      )

      when(mockFunction.apply(any[Set[Int]])).thenThrow(new RuntimeException("t2 failed"))

      val actorName = UUID.randomUUID().toString
      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) => }
      expectMsgPF() { case TransitionFailed(_, 2, _, _, _, _, protocol.ExceptionStrategy.RetryWithDelay(Delay)) => }

      // verify that the mock function was called
      verify(mockFunction).apply(any[Set[Int]])

      // kill the actor
      actor ! Stop(delete = false)
      syncKillActorWithPoisonPill(actor)

      // reset the mock
      reset(mockFunction)
      when(mockFunction.apply(any[Set[Int]])).thenReturn(Added(1))

      // create a new actor with the same persistent identifier
      val newActor = createProcessInstance[Set[Int], Event](petriNet, runtime, actorName)

      // TODO find a way to prevent this sleep, perhaps listen on the event bus?
      Thread.sleep(dilatedMillis(1000))

      verify(mockFunction).apply(any[Set[Int]])
    }

    "Block a transition if the exception strategy function throws an exception" in new TestSequenceNet {

      val faultyExceptionHandler: TransitionExceptionHandler[Place] = {
        case (_, _, _) => throw new IllegalStateException("Expected test failure")
      }

      override def sequence =
        Seq(
          transition(exceptionHandler = faultyExceptionHandler)(_ => throw new IllegalArgumentException("Failed!"))
        )

      val actorName = UUID.randomUUID().toString
      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(initialMarking, Set.empty)

      expectMsgClass(classOf[Initialized])

      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, protocol.ExceptionStrategy.BlockTransition) => }
    }

    "Not re-fire a failed transition with 'Blocked' strategy after being restored from persistent storage" in new TestSequenceNet {

      // setup a failing mock function
      val mockT2 = mock[Set[Int] => Event]
      when(mockT2.apply(any[Set[Int]])).thenThrow(new RuntimeException("t2 mock failed"))

      override val sequence = Seq(
        transition(automated = true)(_ => Added(1)),
        transition(automated = true)(mockT2)
      )

      val recipeInstanceId = UUID.randomUUID().toString

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime, recipeInstanceId)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      // expect the next marking: p2 -> 1
      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) => }
      expectMsgPF() { case TransitionFailed(_, 2, _, _, _, _, protocol.ExceptionStrategy.BlockTransition) => }

      verify(mockT2).apply(any[Set[Int]])

      // terminate the actor
      syncKillActorWithPoisonPill(actor)

      reset(mockT2)

      // create a new actor with the same persistent identifier
      val newActor = createProcessInstance[Set[Int], Event](petriNet, runtime, recipeInstanceId)

      newActor ! GetState

      // assert that the actor is the same as before termination
      expectMsgPF() { case InstanceState(2, _, _, _) => }

      verifyNoMoreInteractions(mockT2)
    }

    "Not execute a transition with scheduled retry after being stopped" in new TestSequenceNet {

      val InitialDelay: Long = dilatedMillis(50)
      val retryHandler: TransitionExceptionHandler[Place] = {
        case (e, n, _) => RetryWithDelay(InitialDelay)
      }

      val mockFunction = mock[Set[Int] => Event]

      override val sequence = Seq(
        transition(automated = true, exceptionHandler = retryHandler)(mockFunction)
      )

      val mockPromise = Promise[Boolean]()

      when(mockFunction.apply(any[Set[Int]])).thenAnswer(new Answer[Event] {
        override def answer(invocationOnMock: InvocationOnMock): Event = {
          mockPromise.complete(Success(true)) // FIXME TRAVIS: sometimes we have PromiseAlreadyCompleted exception here
          throw new RuntimeException("failure")
        }
      })

      val actorName = UUID.randomUUID().toString

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime, actorName)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])
      expectMsgPF() { case TransitionFailed(_, 1, _, _, _, _, protocol.ExceptionStrategy.RetryWithDelay(InitialDelay)) => }

      whenReady(mockPromise.future) { _ =>

        verify(mockFunction).apply(any[Set[Int]]) // FIXME TRAVIS: sometimes executes 2 times

        // kill the actor
        actor ! Stop(delete = false)
        syncKillActorWithPoisonPill(actor)

        Thread.sleep(dilatedMillis(100))

        reset(mockFunction)

        verifyNoInteractions(mockFunction)
      }
    }

    "When Idle terminate after some time if an idle TTL has been specified" in new TestSequenceNet {

      val ttl = FiniteDuration(500, MILLISECONDS).dilated

      val customSettings = instanceSettings.copy(idleTTL = Some(ttl))

      override val sequence = Seq(
        transition(automated = false)(_ => Added(1)),
        transition(automated = false)(_ => Added(2))
      )

      val petriNetActor = createPetriNetActor(processInstanceProps(petriNet, runtime, customSettings, null), UUID.randomUUID().toString)
      watch(petriNetActor)

      implicit val timeout = Timeout(dilatedMillis(2000), MILLISECONDS)

      petriNetActor ! Initialize(initialMarking, null)
      expectMsgClass(classOf[Initialized])
    }

    "fire automated transitions in parallel when possible" in new StateTransitionNet[Unit, Unit] {

      override val eventSourceFunction: Unit => Unit => Unit = s => e => s

      val p1 = place(id = 1)
      val p2 = place(id = 2)

      val t1 = nullTransition(id = 1, automated = false)
      val t2 = stateTransition(id = 2, automated = true)(_ => Thread.sleep(dilatedMillis(500)))
      val t3 = stateTransition(id = 3, automated = true)(_ => Thread.sleep(dilatedMillis(500)))

      val petriNet = createPetriNet[Unit](
        t1 ~> p1,
        t1 ~> p2,
        p1 ~> t2,
        p2 ~> t3
      )

      // creates a petri net actor with initial marking: p1 -> 1
      val initialMarking = Marking.empty[Place]

      val actor = createProcessInstance[Unit, Unit](petriNet, runtime)

      actor ! Initialize(initialMarking, null)
      expectMsgClass(classOf[Initialized])

      // fire the first transition manually
      actor ! FireTransition(transitionId = 1, input = null)

      expectMsgPF() { case TransitionFired(_, 1, _, _, _, _, _) => }

      import org.scalatest.concurrent.TimeLimits._

      failAfter(Span(dilatedMillis(1000), Milliseconds)) {

        // expect that the two subsequent transitions are fired automatically and in parallel (in any order)
        expectMsgInAnyOrderPF(
          { case TransitionFired(_, 2, _, _, _, _, _) => },
          { case TransitionFired(_, 3, _, _, _, _, _) => }
        )
      }
    }
    "Reject DelayedTransitionFired after not receiving a TransitionDelayed" in new TestSequenceNet {

      override val sequence = Seq(
        transition() { _ => Added(1) })

      val actor = createProcessInstance[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(initialMarking, Set.empty)
      expectMsgClass(classOf[Initialized])

      val receiver = TestProbe()

      actor.tell(DelayedTransitionFired(jobId = 1, transitionId = 1, "EventToFire"), receiver.testActor)

      receiver.expectNoMessage()
    }

    "Should correctly determine the OutputEventName for Delayed Transitions" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy = BlockInteraction

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val logMock = mock[DiagnosticLoggingAdapter]

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      assert(output == eventName)
    }

    "Should fail to determine the OutputEventName for Delayed Transitions if there are 2 outcomes" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"
      val eventName2 = "orignalEvent2"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(eventName2, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy = BlockInteraction

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val logMock = mock[DiagnosticLoggingAdapter]

      var exceptionThrown = false

      try {
        ProcessInstance.getOutputEventName(interactionTransition, logMock)
      } catch {
        case e: FatalInteractionException => exceptionThrown = true
      }
      assert(exceptionThrown)
    }

    "Should correctly determine the OutputEventName for Delayed Transitions if FireEventAfterFailure retry strategy is used" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"
      val exhaustedEvent = "exhaustedEvent"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(exhaustedEvent, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy = FireEventAfterFailure(EventDescriptor(exhaustedEvent, Seq.empty))

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val logMock = mock[DiagnosticLoggingAdapter]

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      assert(output == eventName)
    }

    "Should correctly determine the OutputEventName for Delayed Transitions if RetryWithIncrementalBackoff is used with FireEvent" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"
      val exhaustedEvent = "exhaustedEvent"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty),
        EventDescriptor(exhaustedEvent, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy =
        RetryWithIncrementalBackoff(Zero, 1.0, 1, Option.empty, Some(EventDescriptor(exhaustedEvent, Seq.empty)))

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val logMock = mock[DiagnosticLoggingAdapter]

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      assert(output == eventName)
    }

    "Should correctly determine the OutputEventName for Delayed Transitions if RetryWithIncrementalBackoff is used without FireEvent" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"
      val exhaustedEvent = "exhaustedEvent"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val failureStrategy: InteractionFailureStrategy =
        RetryWithIncrementalBackoff(Zero, 1.0, 1, Option.empty, Option.empty)

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq.empty,
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        failureStrategy, Map.empty, false)

      val logMock = mock[DiagnosticLoggingAdapter]

      val output: String = ProcessInstance.getOutputEventName(interactionTransition, logMock)

      assert(output == eventName)
    }

    "Should get correct wait time from state (Java Duration)" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[Duration])),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val ingredients = Map[String, Value]("waitTime" -> Converters.toValue(Duration.ofMillis(60000L)))
      val output: Long = ProcessInstance.getWaitTimeInMillis(interactionTransition, RecipeInstanceState("id", "id", ingredients, Map.empty[String, String], Seq.empty))

      assert(output == 60000L)
    }

    "Should get correct wait time from state (Scala FiniteDuration)" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[FiniteDuration])),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val ingredients = Map[String, Value]("waitTime" -> Converters.toValue(FiniteDuration.apply(60000L, TimeUnit.MILLISECONDS)))

      val output: Long = ProcessInstance.getWaitTimeInMillis(interactionTransition, RecipeInstanceState("id", "id", ingredients, Map.empty[String, String], Seq.empty))

      assert(output == 60000L)
    }

    "Should get correct wait time from the predefined ingredients" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[Duration])),
        "Name",
        "Name",
        Map[String, Value]("waitTime" -> Converters.toValue(Duration.ofMillis(60000L))),
        Option.empty,
        BlockInteraction, Map.empty, false)

      val ingredients = Map[String, Value]("waitTime" -> Converters.toValue(Duration.ofMillis(1200000L)))

      val output: Long = ProcessInstance.getWaitTimeInMillis(interactionTransition, RecipeInstanceState("id", "id", ingredients, Map.empty[String, String], Seq.empty))

      assert(output == 60000L)
    }

    "Should reject getting the wait time if there is more then 1 ingredient" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", Converters.readJavaType[Duration]),
          IngredientDescriptor("waitTime2", Converters.readJavaType[Duration])),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val ingredients = Map[String, Value]("waitTime" -> Converters.toValue(Duration.ofMillis(60000L)))

      var exceptionThrown = false
      try {
        ProcessInstance.getWaitTimeInMillis(interactionTransition, RecipeInstanceState("id", "id", ingredients, Map.empty[String, String], Seq.empty))
      } catch {
        case _: FatalInteractionException => exceptionThrown = true
      }
      assert(exceptionThrown)
    }

    "Should reject getting the wait time if the ingredient is the wrong type" in new TestSequenceNet {
      override val sequence = Seq(
        transition() { _ => Added(1) })

      val eventName = "originalEvent1"

      val eventsToFire: Seq[EventDescriptor] = Seq(
        EventDescriptor(eventName, Seq.empty)
      )

      val interactionTransition: InteractionTransition = InteractionTransition(
        eventsToFire, eventsToFire,
        Seq(IngredientDescriptor("waitTime", types.Bool)),
        "Name",
        "Name",
        Map.empty,
        Option.empty,
        BlockInteraction, Map.empty, false)

      val ingredients = Map[String, Value]("waitTime" -> Converters.toValue(false))
      var exceptionThrown = false
      try {
        ProcessInstance.getWaitTimeInMillis(interactionTransition, RecipeInstanceState("id", "id", ingredients, Map.empty[String, String], Seq.empty))
      } catch {
        case _: FatalInteractionException => exceptionThrown = true
      }
      assert(exceptionThrown)
    }
  }
}
