package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{Actor, ActorRef, ActorSystem, PoisonPill, Props}
import akka.pattern.ask
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import akka.util.Timeout
import com.ing.baker.il.petrinet.{EventTransition, Place, RecipePetriNet, Transition}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor, IngredientDescriptor}
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol.FireDelayedTransition
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.CheckForProcessesToBeDeleted
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventReaction.NotifyWhenReceived
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.recipe_manager.RecipeManager
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceCreated, RecipeInstanceState}
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types
import com.ing.baker.types.Value
import com.typesafe.config.{Config, ConfigFactory}
import io.prometheus.client.CollectorRegistry
import org.mockito.ArgumentMatchers.anyString
import org.mockito.Mockito
import org.mockito.Mockito.when
import org.scalatest.concurrent.Eventually
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar
import scalax.collection.immutable.Graph

import java.util.UUID
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

object ProcessIndexSpec {
  val config: Config = ConfigFactory.parseString(
    """
      |akka.actor.allow-java-serialization = off
      |baker.actor.snapshot-interval = 1
      |akka.persistence.journal.plugin = "inmemory-journal"
      |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |akka.test.timefactor = 3.0
    """.stripMargin)
}

//noinspection TypeAnnotation
class ProcessIndexSpec extends TestKit(ActorSystem("ProcessIndexSpec", ProcessIndexSpec.config))
  with ImplicitSender
  with AnyWordSpecLike
  with Matchers
  with BeforeAndAfterAll
  with BeforeAndAfter
  with MockitoSugar
  with Eventually {

  val noMsgExpectTimeout: FiniteDuration = 100.milliseconds

  val otherMsg = mock[ProcessInstanceProtocol.Command]

  before {
    Mockito.reset(otherMsg)
  }

  override def beforeAll() = {
    super.beforeAll()
    CollectorRegistry.defaultRegistry.clear()
  }

  override def afterAll(): Unit = {
    super.afterAll()
    TestKit.shutdownActorSystem(system)
  }

  val recipeId: String = UUID.randomUUID().toString

  val baseRecipe: CompiledRecipe = CompiledRecipe(
    name = "name",
    recipeId = recipeId,
    petriNet = new PetriNet(Graph.empty),
    initialMarking = Marking.empty,
    validationErrors = Seq.empty,
    eventReceivePeriod = Option.empty,
    retentionPeriod = Option.empty)

  val recipeManager: RecipeManager = {
    val manager = mock[RecipeManager]
    when(manager.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(baseRecipe, updated = 0L))))
    manager
  }

  /**
   * A helper function to synchronously create a process instance.
   * This handles the asynchronous ask-reply handshake between ProcessIndex and the mock ProcessInstance actor.
   * It returns the Initialize message that was sent to the mock actor.
   */
  def createProcessAndWait(
                            actorIndex: ActorRef,
                            probe: TestProbe, // The probe that will act as the mock ProcessInstance
                            recipeId: String,
                            recipeInstanceId: String,
                            metadata: Map[String, String] = Map.empty
                          ): Initialize = {
    actorIndex ! CreateProcess(recipeId, recipeInstanceId, metadata)

    val initializeMsg = probe.expectMsgClass(classOf[Initialize])

    probe.reply(Initialized(initializeMsg.marking, initializeMsg.state))

    expectMsgClass(classOf[RecipeInstanceCreated])

    initializeMsg
  }

  "ProcessIndex" should {

    "create the PetriNetInstance actor when Initialize message is received" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val expectedInitializeMsg =
        Initialize(Marking.empty[Place], RecipeInstanceState(recipeId, recipeInstanceId, Map.empty[String, Value], Map.empty[String, String], List.empty))
      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)

      val receivedInitializeMsg = createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      receivedInitializeMsg shouldBe expectedInitializeMsg
    }

    "create the PetriNetInstance actor with given metadata when Initialize message is received" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val metadata = Map("someKey" -> "someValue")
      val expectedInitializeMsg =
        Initialize(Marking.empty[Place], RecipeInstanceState(
          recipeId = recipeId,
          recipeInstanceId = recipeInstanceId,
          ingredients = Map(RecipeInstanceMetadataName -> com.ing.baker.types.Converters.toValue(metadata)),
          recipeInstanceMetadata = metadata,
          events = List.empty))
      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)

      val receivedInitializeMsg = createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId, metadata)

      receivedInitializeMsg shouldBe expectedInitializeMsg
    }

    "passivation" in {
      val duration = 5.seconds

      implicit val timeout = Timeout(duration)

      val recipeInstanceId = UUID.randomUUID().toString

      val petriNetActorProbe: ActorRef = system.actorOf(Props(new Actor {
        override def receive: Receive = {
          case init: Initialize => sender() ! Initialized(init.marking, init.state)
          case _ =>
        }
      }), recipeInstanceId)

      val actorIndex: ActorRef = createActorIndex(petriNetActorProbe, recipeManager)
      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      expectMsgClass(classOf[RecipeInstanceCreated])

      eventually {
        val result = Await.result((actorIndex ? GetIndex).mapTo[Index], duration)
        result.entries.size shouldBe 1
      }

      petriNetActorProbe ! PoisonPill

      eventually {
        val result = Await.result((actorIndex ? GetIndex).mapTo[Index], duration)
        result.entries.size shouldBe 0
      }

      actorIndex ! PoisonPill

      val afterSnapshotRead: ActorRef = createActorIndex(petriNetActorProbe, recipeManager)
      val result = Await.result((afterSnapshotRead ? GetIndex).mapTo[Index], duration)
      result.entries.size shouldBe 0
    }

    "not create the PetriNetInstance actor if already created" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)

      createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      expectMsg(ProcessAlreadyExists(recipeInstanceId))
      petriNetActorProbe.expectNoMessage(noMsgExpectTimeout) // Ensure no second Initialize message is sent
    }

    "delete a process if a retention period is defined, CheckForProcessesToBeDeleted received" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val recipeRetentionPeriod = 500.milliseconds
      val processProbe = TestProbe(recipeInstanceId)

      val recipeWithRetention = baseRecipe.copy(retentionPeriod = Some(recipeRetentionPeriod))
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(recipeWithRetention, updated = 0L))))

      val actorIndex = createActorIndex(processProbe.ref, recipeManagerMock)
      createProcessAndWait(actorIndex, processProbe, recipeId, recipeInstanceId)

      Thread.sleep(recipeRetentionPeriod.toMillis)
      actorIndex ! CheckForProcessesToBeDeleted
      processProbe.expectMsg(15.seconds, Stop(delete = true))

      processProbe.ref ! PoisonPill

      val probe2 = TestProbe()
      probe2.send(actorIndex, GetProcessState(recipeInstanceId))
      probe2.expectMsg(10.seconds, ProcessDeleted(recipeInstanceId))
    }

    "forget a process if a remember duration is defined and this is passed" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val recipeRetentionPeriod = 500.milliseconds
      val processProbe = TestProbe(recipeInstanceId)

      val recipeWithRetention = baseRecipe.copy(retentionPeriod = Some(recipeRetentionPeriod))
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(recipeWithRetention, updated = 0L))))

      val actorIndex = createActorIndex(processProbe.ref, recipeManagerMock, Some(1.milliseconds))
      createProcessAndWait(actorIndex, processProbe, recipeId, recipeInstanceId)

      Thread.sleep(recipeRetentionPeriod.toMillis)
      actorIndex ! CheckForProcessesToBeDeleted
      processProbe.expectMsg(15.seconds, Stop(delete = true))

      processProbe.ref ! PoisonPill

      Thread.sleep(100)

      actorIndex ! CheckForProcessesToBeDeleted

      val probe2 = TestProbe()
      probe2.send(actorIndex, GetProcessState(recipeInstanceId))
      probe2.expectMsg(10.seconds, NoSuchProcess(recipeInstanceId))
    }

    "Forward the FireTransition command when a valid HandleEvent is sent" in {
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeInstanceId = UUID.randomUUID().toString
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, isSensoryEvent = true, None))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      when(petrinetMock.transitions).thenReturn(transitions)

      val recipeManagerMock = mock[RecipeManager]
      val recipe = baseRecipe.copy(petriNet = petrinetMock)
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(recipe, updated = 0L))))

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerMock)
      createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      val runtimeEvent = EventInstance("Event", Map.empty)
      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      petriNetActorProbe.expectMsgAllClassOf(classOf[FireTransition])
    }

    "reply with a NoSuchProcess rejection message when attempting to fire an event to a not existing process" in {
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(baseRecipe, updated = 0L))))

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerMock)
      val recipeInstanceId = UUID.randomUUID().toString
      val runtimeEvent = EventInstance("Event", Map.empty)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      expectMsg(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
    }

    "reply with an InvalidEvent rejection message when attempting to fire an event that is not know in the compiledRecipe" in {
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeInstanceId = UUID.randomUUID().toString

      // baseRecipe has an empty petrinet, so it has no sensory events. This is correct for the test.
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(baseRecipe.copy(name = "name"), 0L))))

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerMock)
      createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      val runtimeEvent = EventInstance("Event", Map.empty)
      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      expectMsg(FireSensoryEventRejection.InvalidEvent(recipeInstanceId, s"No event with name 'Event' found in recipe 'name'"))
    }

    "reply with an InvalidEvent rejection message when attempting to fire an event that does not comply to the recipe" in {
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeInstanceId = UUID.randomUUID().toString
      val eventType = EventDescriptor("Event", Seq(IngredientDescriptor("ingredientName", types.CharArray)))
      val transitions: Set[Transition] = Set(EventTransition(eventType, isSensoryEvent = true, None))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      when(petrinetMock.transitions).thenReturn(transitions)

      val recipe = baseRecipe.copy(petriNet = petrinetMock)
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(recipe, updated = 0L))))

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerMock)
      createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      val runtimeEvent = EventInstance("Event", Map.empty)
      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      expectMsg(FireSensoryEventRejection.InvalidEvent(recipeInstanceId, s"Invalid event: no value was provided for ingredient 'ingredientName'"))
    }

    "reply with an EventReceivePeriodExpired rejection message when attempting to fire an event after expiration period" in {
      val receivePeriodTimeout = 1000 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeInstanceId = UUID.randomUUID().toString
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, isSensoryEvent = true, None))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      when(petrinetMock.transitions).thenReturn(transitions)

      val recipe = baseRecipe.copy(
        petriNet = petrinetMock,
        eventReceivePeriod = Some(receivePeriodTimeout))
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(recipe, updated = 0L))))

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerMock)
      createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      val runtimeEvent = EventInstance("Event", Map.empty)
      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)
      petriNetActorProbe.expectMsgAllClassOf(classOf[FireTransition])

      Thread.sleep(receivePeriodTimeout.toMillis * 2)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)
      petriNetActorProbe.expectNoMessage(noMsgExpectTimeout)

      expectMsg(FireSensoryEventRejection.ReceivePeriodExpired(recipeInstanceId))
    }

    "Forward the DelayedTransitionFired command when a FireDelayedTransition is received" in {
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeInstanceId = UUID.randomUUID().toString
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, isSensoryEvent = true, None))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      when(petrinetMock.transitions).thenReturn(transitions)

      val recipe = baseRecipe.copy(petriNet = petrinetMock)
      val recipeManagerMock = mock[RecipeManager]
      when(recipeManagerMock.get(anyString())).thenReturn(Future.successful(Some(RecipeRecord.of(recipe, updated = 0L))))

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerMock)
      val jobId: Long = 1
      val transitionId: Long = 2
      val eventToFire = "EventToFire"

      createProcessAndWait(actorIndex, petriNetActorProbe, recipeId, recipeInstanceId)

      val receiverProbe = TestProbe()
      actorIndex ! FireDelayedTransition(recipeInstanceId, jobId, transitionId, eventToFire, receiverProbe.testActor)
      petriNetActorProbe.expectMsg(DelayedTransitionFired(jobId, transitionId, eventToFire))
    }
  }

  private def createActorIndex(petriNetActorRef: ActorRef,
                               recipeManager: RecipeManager,
                               rememberProcessDuration: Option[Duration] = None): ActorRef = {
    val props = Props(new ProcessIndex(
      recipeInstanceIdleTimeout = None,
      retentionCheckInterval = None,
      configuredEncryption = Encryption.NoEncryption,
      interactionManager = CachingInteractionManager(),
      recipeManager = recipeManager,
      Seq.empty,
      Seq.empty,
      Seq.empty,
      rememberProcessDuration) {
      override def createProcessActor(id: String, compiledRecipe: CompiledRecipe) = {
        context.watchWith(petriNetActorRef, TerminatedWithReplyTo(petriNetActorRef))
        petriNetActorRef
      }
      override def getProcessActor(recipeInstanceId: String): Option[ActorRef] = {
        Some(petriNetActorRef)
      }
      override def getRecipeIdFromActor(actorRef: ActorRef): String = {
        val result = if (petriNetActorRef.path.name.size >= 36) petriNetActorRef.path.name.substring(0, 36) else petriNetActorRef.path.name
        result
      }
    })
    system.actorOf(props, s"actorIndex-${UUID.randomUUID().toString}")
  }
}