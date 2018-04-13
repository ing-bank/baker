package com.ing.baker.runtime.core

import java.util.UUID

import akka.actor.ActorRef
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.TestProbe
import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.core.events.RejectReason._
import com.ing.baker.runtime.core.events._
import com.ing.baker.types.PrimitiveValue
import org.hamcrest
import org.hamcrest.Description
import org.mockito.Matchers
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.language.postfixOps


object BakerEventsSpec {

  def matchPF[T](pf: PartialFunction[T, Any]) = Matchers.argThat(new hamcrest.BaseMatcher[T] {
    override def matches(o: scala.Any): Boolean = pf.isDefinedAt(o.asInstanceOf[T])

    override def describeTo(description: Description): Unit = {
      description.appendValue(pf)
    }
  })

  def listenerFunction(probe: ActorRef): PartialFunction[BakerEvent, Unit] = {
    case e: BakerEvent =>
      println(s"Listener consumed event $e")
      probe ! e
  }

  def expectMsgInAnyOrderPF[Out](testProbe: TestProbe, pfs: PartialFunction[Any, Out]*): Unit = {
    if (pfs.nonEmpty) {
      val total = pfs.reduce((a, b) ⇒ a.orElse(b))
      testProbe.expectMsgPF() {
        case msg@_ if total.isDefinedAt(msg) ⇒
          val index = pfs.indexWhere(pf ⇒ pf.isDefinedAt(msg))
          val pfn = pfs(index)
          pfn(msg)
          expectMsgInAnyOrderPF[Out](testProbe, pfs.take(index) ++ pfs.drop(index + 1): _*)
      }
    }
  }

  protected def getRecipe(recipeName: String): Recipe =
    Recipe(recipeName)
      .withInteractions(
        interactionOne
          .withOverriddenOutputIngredientName("interactionOneIngredient")
          .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(initialDelay = 10 millisecond, maximumRetries = 3)),
        interactionTwo
          .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"),
        interactionThree
          .withMaximumInteractionCount(1),
        interactionFour
          .withRequiredEvents(secondEvent, eventFromInteractionTwo),
        interactionFive,
        interactionSix,
        providesNothingInteraction,
        sieveInteraction
      )
      .withSensoryEvents(
        initialEvent.withMaxFiringLimit(1),
        initialEventExtendedName,
        secondEvent,
        notUsedSensoryEvent)

}

class BakerEventsSpec extends TestRecipeHelper {

  import BakerEventsSpec._

  override def actorSystemName = "BakerEventsSpec"

  val log = LoggerFactory.getLogger(classOf[BakerEventsSpec])

  val eventReceiveTimeout = 1 seconds

  before {
    resetMocks
    setupMockResponse()

    // Clean inmemory-journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(defaultActorSystem).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

  "Baker" should {

    "notify ProcessCreated/EventReceived/InteractionStarted/InteractionCompleted events" in {
      val recipeName = "EventReceivedEventRecipe"
      val processId = UUID.randomUUID().toString
      val (baker, recipeId) = setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)

      val listenerProbe = TestProbe()

      baker.registerEventListenerPF(listenerFunction(listenerProbe.ref))

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue), Some("someId"))

      listenerProbe.expectMsgPF(eventReceiveTimeout) {
        case ProcessCreated(_, `recipeId`, `recipeName`, `processId`) =>
      }

      listenerProbe.expectMsgPF(eventReceiveTimeout) {
        case msg@EventReceived(_, `processId`, Some("someId"), RuntimeEvent("InitialEvent", Seq(Tuple2("initialIngredient", PrimitiveValue(`initialIngredientValue`))))) => msg
      }

      expectMsgInAnyOrderPF(listenerProbe,
        { case msg@InteractionStarted(_, `processId`, "SieveInteraction") => msg },
        { case msg@InteractionStarted(_, `processId`, "InteractionOne") => msg },
        { case msg@InteractionStarted(_, `processId`, "InteractionTwo") => msg },
        { case msg@InteractionStarted(_, `processId`, "InteractionThree") => msg },
        { case msg@InteractionStarted(_, `processId`, "ProvidesNothingInteraction") => msg},
        { case msg@InteractionCompleted(_, _, `processId`, "InteractionOne", RuntimeEvent("InteractionOneSuccessful", Seq(Tuple2("interactionOneIngredient",PrimitiveValue("interactionOneIngredient"))))) => msg },
        { case msg@InteractionCompleted(_, _, `processId`, "InteractionTwo", RuntimeEvent("EventFromInteractionTwo", Seq(Tuple2("interactionTwoIngredient", PrimitiveValue("interactionTwoIngredient"))))) => msg },
        { case msg@InteractionCompleted(_, _, `processId`, "InteractionThree", RuntimeEvent("InteractionThreeSuccessful", Seq(Tuple2("interactionThreeIngredient", PrimitiveValue("interactionThreeIngredient"))))) => msg },
        { case msg@InteractionCompleted(_, _, `processId`, "ProvidesNothingInteraction", RuntimeEvent("ProvidesNothingInteraction", Seq())) => msg },
        { case msg@InteractionCompleted(_, _, `processId`, "SieveInteraction", RuntimeEvent("SieveInteractionSuccessful", Seq(Tuple2("sievedIngredient", PrimitiveValue("sievedIngredient"))))) => msg }
      )

      listenerProbe.expectNoMessage(eventReceiveTimeout)
    }

    "notify EventRejected event with InvalidEvent reason" in {
      val recipeName = "EventRejectedEventRecipe"
      val processId = UUID.randomUUID().toString
      val (baker, recipeId) = setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)

      val listenerProbe = TestProbe()

      baker.registerEventListenerPF(listenerFunction(listenerProbe.ref))

      baker.bake(recipeId, processId)

      // We used async function here because ThirdEvent is not part of the recipe and throws exception
      baker.processEventAsync(processId, ThirdEvent(), Some("someId"))

      listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
        case EventRejected(_, `processId`, Some("someId"), RuntimeEvent("ThirdEvent", Seq()), InvalidEvent) =>
      }

      listenerProbe.expectNoMessage(eventReceiveTimeout)
    }

    "notify EventRejected event with AlreadyReceived reason" in {
      val recipeName = "AlreadyReceivedRecipe"
      val processId = UUID.randomUUID().toString
      val (baker, recipeId) = setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)

      val listenerProbe = TestProbe()

      baker.registerEventListenerPF(listenerFunction(listenerProbe.ref))

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue), Some("someId"))
      baker.processEvent(processId, InitialEvent(initialIngredientValue), Some("someId")) // Same correlationId cannot be used twice

      listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
        case EventRejected(_, `processId`, Some("someId"), RuntimeEvent("InitialEvent", Seq(Tuple2("initialIngredient", PrimitiveValue(`initialIngredientValue`)))), AlreadyReceived) =>
      }

      listenerProbe.expectNoMessage(eventReceiveTimeout)
    }

    "notify EventRejected event with FiringLimitMet reason" in {
      val recipeName = "FiringLimitMetRecipe"
      val processId = UUID.randomUUID().toString
      val (baker, recipeId) = setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)

      val listenerProbe = TestProbe()

      baker.registerEventListenerPF(listenerFunction(listenerProbe.ref))

      baker.bake(recipeId, processId)
      baker.processEvent(processId, InitialEvent(initialIngredientValue))
      baker.processEvent(processId, InitialEvent(initialIngredientValue)) // Firing limit is set to 1 in the recipe

      listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
        case EventRejected(_, `processId`, None, RuntimeEvent("InitialEvent", Seq(Tuple2("initialIngredient", PrimitiveValue(`initialIngredientValue`)))), FiringLimitMet) =>
      }

      listenerProbe.expectNoMessage(eventReceiveTimeout)
    }

    "notify EventRejected event with ReceivePeriodExpired reason" in {
      val recipeName = "ReceivePeriodExpiredRecipe"
      val processId = UUID.randomUUID().toString
      val (baker, recipeId) = setupBakerWithRecipe(getRecipe(recipeName).withEventReceivePeriod(eventReceiveTimeout), mockImplementations)

      val listenerProbe = TestProbe()

      baker.registerEventListenerPF(listenerFunction(listenerProbe.ref))

      baker.bake(recipeId, processId)

      Thread.sleep(eventReceiveTimeout.toMillis)

      baker.processEvent(processId, InitialEvent(initialIngredientValue), Some("someId"))

      listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
        case EventRejected(_, `processId`, Some("someId"), RuntimeEvent("InitialEvent", Seq(Tuple2("initialIngredient", PrimitiveValue(`initialIngredientValue`)))), ReceivePeriodExpired) =>
      }

      listenerProbe.expectNoMessage(eventReceiveTimeout)
    }

  }
}
