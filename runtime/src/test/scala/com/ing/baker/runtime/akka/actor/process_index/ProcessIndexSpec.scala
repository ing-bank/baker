package com.ing.baker.runtime.akka.actor.process_index

import java.util.UUID

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.testkit.{ImplicitSender, TestKit, TestProbe}
import com.ing.baker.il.petrinet.{EventTransition, Place, RecipePetriNet, Transition}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor, IngredientDescriptor}
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.CheckForProcessesToBeDeleted
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventReaction.NotifyWhenReceived
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol.{AllRecipes, GetAllRecipes, RecipeInformation}
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.akka.internal.InteractionManagerLocal
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}
import com.ing.baker.types
import com.ing.baker.types.Value
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
      |akka.actor.allow-java-serialization = off
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
      case GetAllRecipes =>
        sender ! AllRecipes(Seq[RecipeInformation](
          RecipeInformation(CompiledRecipe("name", recipeId, new PetriNet(Graph.empty), Marking.empty, Seq.empty, Option.empty, Option.empty), 0L)))
    }
  }))

  val processActorMock = system.actorOf(Props(new Actor() {
    override def receive: Receive = {
      case _ => ()
    }
  }))

  "ProcessIndex" should {

    "create the PetriNetInstance actor when Initialize message is received" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val initializeMsg =
        Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))
      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)
      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      petriNetActorProbe.expectMsg(initializeMsg)
    }

    "not create the PetriNetInstance actor if already created" in {
      val recipeInstanceId = UUID.randomUUID().toString
      val initializeMsg = Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))
      val petriNetActorProbe = TestProbe()
      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManager)
      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      petriNetActorProbe.expectMsg(initializeMsg)
      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      petriNetActorProbe.expectNoMessage(noMsgExpectTimeout)
      expectMsg(ProcessAlreadyExists(recipeInstanceId))
    }

    "delete a process if a retention period is defined, stop command is received" in {
      val recipeRetentionPeriod = 500 milliseconds
      val processProbe = TestProbe()
      val recipeManagerProbe = TestProbe()
      val actorIndex = createActorIndex(processProbe.ref, recipeManagerProbe.ref)
      val recipeInstanceId = UUID.randomUUID().toString
      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
        CompiledRecipe("name", recipeId, new PetriNet(Graph.empty), Marking.empty, Seq.empty,
          Option.empty, Some(recipeRetentionPeriod)), 0L))))
      val initializeMsg = Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))
      processProbe.expectMsg(initializeMsg)
      Thread.sleep(recipeRetentionPeriod.toMillis)
      // inform the index to check for processes to be cleaned up
      actorIndex ! CheckForProcessesToBeDeleted
      processProbe.expectMsg(15 seconds, Stop(delete = true))
    }

    "Forward the FireTransition command when a valid HandleEvent is sent" in {

      val petriNetActorProbe = TestProbe("petrinet-probe")

      val recipeManagerProbe = TestProbe()

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val recipeInstanceId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(CompiledRecipe("name", recipeId, petrinetMock, Marking.empty,
          Seq.empty, Option.empty, Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val runtimeEvent = EventInstance("Event", Map.empty)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      petriNetActorProbe.expectMsgAllClassOf(classOf[FireTransition])

    }

    "reply with a NoSuchProcess rejection message when attempting to fire an event to a not existing process" in {

      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeManagerProbe = TestProbe("recipe-manager-probe")

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val recipeInstanceId = UUID.randomUUID().toString

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      val runtimeEvent = EventInstance("Event", Map.empty)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      expectMsg(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
    }

    "reply with an InvalidEvent rejection message when attempting to fire an event that is now know in the compiledRecipe" in {

      val receivePeriodTimeout = 500 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeManagerProbe = TestProbe("recipe-manager-probe")

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val recipeInstanceId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))

      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      recipeManagerProbe.expectMsg(GetAllRecipes)

      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
          CompiledRecipe("name", recipeId, new PetriNet(Graph.empty), Marking.empty, Seq.empty,
            Some(receivePeriodTimeout), Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val runtimeEvent = EventInstance("Event", Map.empty)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      expectMsg(FireSensoryEventRejection.InvalidEvent(recipeInstanceId ,s"No event with name 'Event' found in recipe 'name'"))
    }

    "reply with an InvalidEvent rejection message when attempting to fire an event that does not comply to the recipe" in {

      val receivePeriodTimeout = 500 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeManagerProbe = TestProbe("recipe-manager-probe")

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val recipeInstanceId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq(IngredientDescriptor("ingredientName", types.CharArray)))
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
          CompiledRecipe("name", recipeId, petrinetMock, Marking.empty, Seq.empty, Some(receivePeriodTimeout), Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val runtimeEvent = EventInstance("Event", Map.empty)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      expectMsg(FireSensoryEventRejection.InvalidEvent(recipeInstanceId ,s"Invalid event: no value was provided for ingredient 'ingredientName'"))
    }

    "reply with an EventReceivePeriodExpired rejection message when attempting to fire an event after expiration period" in {

      val receivePeriodTimeout = 1000 milliseconds
      val petriNetActorProbe = TestProbe("petrinet-probe")
      val recipeManagerProbe = TestProbe("recipe-manager-probe")

      val actorIndex = createActorIndex(petriNetActorProbe.ref, recipeManagerProbe.ref)

      val recipeInstanceId = UUID.randomUUID().toString

      val initializeMsg = Initialize(Marking.empty[Place], RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, true, None))
      when(petrinetMock.transitions).thenReturn(transitions)

      actorIndex ! CreateProcess(recipeId, recipeInstanceId)
      recipeManagerProbe.expectMsg(GetAllRecipes)
      recipeManagerProbe.reply(AllRecipes(Seq[RecipeInformation](
        RecipeManagerProtocol.RecipeInformation(
          CompiledRecipe("name", recipeId, petrinetMock, Marking.empty, Seq.empty,
            Some(receivePeriodTimeout), Option.empty), 0L))))

      petriNetActorProbe.expectMsg(initializeMsg)

      val runtimeEvent = EventInstance("Event", Map.empty)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      petriNetActorProbe.expectMsgAllClassOf(classOf[FireTransition])

      Thread.sleep(receivePeriodTimeout.toMillis * 2)

      actorIndex ! ProcessEvent(recipeInstanceId, runtimeEvent, None, 1 seconds, NotifyWhenReceived)

      petriNetActorProbe.expectNoMessage(noMsgExpectTimeout)

      expectMsg(FireSensoryEventRejection.ReceivePeriodExpired(recipeInstanceId))
    }
  }

  private def createActorIndex(petriNetActorRef: ActorRef, recipeManager: ActorRef): ActorRef = {
    val props = Props(new ProcessIndex(
      recipeInstanceIdleTimeout = None,
      retentionCheckInterval = None,
      configuredEncryption = Encryption.NoEncryption,
      interactionManager = new InteractionManagerLocal(),
      recipeManager = recipeManager,
      Seq.empty) {
      override def createProcessActor(id: String, compiledRecipe: CompiledRecipe) = petriNetActorRef
    })
    system.actorOf(props, s"actorIndex-${UUID.randomUUID().toString}")
  }
}
