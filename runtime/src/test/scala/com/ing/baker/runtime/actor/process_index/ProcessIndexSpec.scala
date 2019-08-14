package com.ing.baker.runtime.actor.process_index

import java.util.UUID

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.stream.testkit.scaladsl.TestSink
import akka.stream.{ActorMaterializer, Materializer}
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import com.ing.baker.il.petrinet.{EventTransition, Place, RecipePetriNet, Transition}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor, IngredientDescriptor}
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.actor.process_index.ProcessIndex.CheckForProcessesToBeDeleted
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol.{AllRecipes, GetAllRecipes, RecipeInformation}
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.core.internal.InteractionManager
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}
import com.ing.baker.types
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Mockito
import org.mockito.Mockito.when
import org.scalatest.concurrent.Eventually
import org.scalatest.mockito.MockitoSugar
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll, Matchers, WordSpecLike}
import scalax.collection.immutable.Graph

import scala.concurrent.duration._

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

  val noMsgExpectTimeout: FiniteDuration = 100.milliseconds

  val otherMsg = mock[ProcessInstanceProtocol.Command]

  before {
    Mockito.reset(otherMsg)
  }

  override def afterAll {
    TestKit.shutdownActorSystem(system)
  }

  val recipeId: String = UUID.randomUUID().toString

  val recipeManager = system.actorOf(Props(new Actor() {
    override def receive: Receive = {
      case GetAllRecipes => {
        sender ! AllRecipes(Seq[RecipeInformation](
          RecipeInformation(CompiledRecipe("name", recipeId, new PetriNet(Graph.empty), Marking.empty, Seq.empty, Option.empty, Option.empty), 0L)))
      }
    }
  }))

  val processActorMock = system.actorOf(Props(new Actor() {
    override def receive: Receive = {
      case _ => ()
    }
  }))

  implicit val materializer: Materializer = ActorMaterializer()

  def expectProcessEventReply(reply: Any): Unit = {

    expectMsgType[ProcessEventResponse]
      .sourceRef
      .runWith(TestSink.probe)
      .requestNext(reply)
      .expectComplete()
  }

  "ProcessIndex" should {

    "create the PetriNetInstance actor when Initialize message is received" in {
      val processId = UUID.randomUUID().toString
      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))

      val petriNetActorProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)

      actorIndex ! CreateProcess(recipeId, processId)

      petriNetActorProbe.expectMsg(initializeMsg)
    }

    "not create the PetriNetInstance actor if already created" in {
      val processId = UUID.randomUUID().toString
      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))

      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)

      actorIndex ! CreateProcess(recipeId, processId)

      petriNetActorProbe.expectMsg(initializeMsg)

      actorIndex ! CreateProcess(recipeId, processId)

      petriNetActorProbe.expectNoMessage(noMsgExpectTimeout)
      expectMsg(ProcessAlreadyExists(processId))
    }


    "delete a process if a retention period is defined, stop command is received" in {

      val recipeRetentionPeriod = 500 milliseconds

      val processProbe = TestProbe()
      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(processProbe.ref, recipeManagerProbe.ref)

      val processId = UUID.randomUUID().toString

      actorIndex ! CreateProcess(recipeId, processId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
        CompiledRecipe("name", recipeId, new PetriNet(Graph.empty), Marking.empty, Seq.empty,
          Option.empty, Some(recipeRetentionPeriod)), 0L))))

      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))
      processProbe.expectMsg(initializeMsg)

      Thread.sleep(recipeRetentionPeriod.toMillis)

      // inform the index to check for processes to be cleaned up
      actorIndex ! CheckForProcessesToBeDeleted

      processProbe.expectMsg(Stop(delete = true))
    }

    "Forward the FireTransition command when a valid HandleEvent is sent" in {

      val petriNetActorProbe = TestProbe("petrinet-probe")

      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val processId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      actorIndex ! CreateProcess(recipeId, processId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(CompiledRecipe("name", recipeId, petrinetMock, Marking.empty,
          Seq.empty, Option.empty, Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val runtimeEvent = new RuntimeEvent("Event", Seq.empty)

      actorIndex ! ProcessEvent(processId, runtimeEvent, None, true, 1 seconds)

      petriNetActorProbe.expectMsgAllClassOf(classOf[FireTransition])

      expectMsgType[ProcessEventResponse]
    }

    "reply with a Unititalized message when attempting to fire an event to a not existing process" in {

      val petriNetActorProbe = TestProbe("petrinet-probe")

      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val processId = UUID.randomUUID().toString

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      val RuntimeEvent = new RuntimeEvent("Event", Seq.empty)

      actorIndex ! ProcessEvent(processId, RuntimeEvent, None, true, 1 seconds)

      expectProcessEventReply(NoSuchProcess(processId))
    }

    "reply with a InvalidEvent message when attempting to fire an event that is now know in the compiledRecipe" in {

      val receivePeriodTimeout = 500 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")

      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val processId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))

      actorIndex ! CreateProcess(recipeId, processId)
      recipeManagerProbe.expectMsg(GetAllRecipes)

      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
          CompiledRecipe("name", recipeId, new PetriNet(Graph.empty), Marking.empty, Seq.empty,
            Some(receivePeriodTimeout), Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val RuntimeEvent = new RuntimeEvent("Event", Seq.empty)

      actorIndex ! ProcessEvent(processId, RuntimeEvent, None, true, 1 seconds)

      expectProcessEventReply(InvalidEvent(processId ,s"No event with name 'Event' found in recipe 'name'"))
    }

    "reply with a InvalidEvent message when attempting to fire an event that does not comply to the recipe" in {

      val receivePeriodTimeout = 500 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")

      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val processId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq(IngredientDescriptor("ingredientName", types.CharArray)))
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      actorIndex ! CreateProcess(recipeId, processId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
          CompiledRecipe("name", recipeId, petrinetMock, Marking.empty, Seq.empty, Some(receivePeriodTimeout), Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val RuntimeEvent = new RuntimeEvent("Event", Seq.empty)

      actorIndex ! ProcessEvent(processId, RuntimeEvent, None, true, 1 seconds)

      expectProcessEventReply(InvalidEvent(processId ,s"Invalid event: no value was provided for ingredient 'ingredientName'"))
    }

    "reply with a EventReceivePeriodExpired message when attempting to fire an event after expiration period" in {

      val receivePeriodTimeout = 1000 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")

      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val processId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], ProcessState(processId, Map.empty, List.empty))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      actorIndex ! CreateProcess(recipeId, processId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
          CompiledRecipe("name", recipeId, petrinetMock, Marking.empty, Seq.empty,
            Some(receivePeriodTimeout), Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val RuntimeEvent = new RuntimeEvent("Event", Seq.empty)

      actorIndex ! ProcessEvent(processId, RuntimeEvent, None, true, 1 seconds)

      petriNetActorProbe.expectMsgAllClassOf(classOf[FireTransition])

      expectMsgType[ProcessEventResponse]

      Thread.sleep(receivePeriodTimeout.toMillis * 2)

      actorIndex ! ProcessEvent(processId, RuntimeEvent, None, true, 1 seconds)

      petriNetActorProbe.expectNoMessage(noMsgExpectTimeout)

      expectProcessEventReply(ReceivePeriodExpired(processId))
    }
  }

  private def createActorIndex(petriNetActorRef: ActorRef,
                               recipeManager: ActorRef): ActorRef = {

    val props = Props(new ProcessIndex(
      processIdleTimeout = None,
      retentionCheckInterval = None,
      configuredEncryption = Encryption.NoEncryption,
      interactionManager = new InteractionManager(),
      recipeManager = recipeManager) {
      override def createProcessActor(id: String, compiledRecipe: CompiledRecipe) = petriNetActorRef
    })

    system.actorOf(props, s"actorIndex-${UUID.randomUUID().toString}")
  }
}
