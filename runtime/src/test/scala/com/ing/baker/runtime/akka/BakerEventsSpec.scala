package com.ing.baker.runtime.akka

import akka.actor.ActorRef
import akka.persistence.inmemory.extension.{ InMemoryJournalStorage, StorageExtension }
import akka.testkit.TestProbe
import com.ing.baker._
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import com.ing.baker.runtime.common.RejectReason._
import com.ing.baker.runtime.scaladsl.{ EventInstance, _ }
import com.ing.baker.types.PrimitiveValue
import com.typesafe.scalalogging.LazyLogging
import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.language.postfixOps


object BakerEventsSpec extends LazyLogging {

  def listenerFunction(probe: ActorRef, logEvents: Boolean = false): PartialFunction[BakerEvent, Unit] = {
    case event: BakerEvent =>
      if (logEvents) {
        logger.info("Listener consumed event {}", event)
      }
      probe ! event
  }

  def expectMsgInAnyOrderPF[Out](testProbe: TestProbe, pfs: PartialFunction[Any, Out]*): Unit = {
    if (pfs.nonEmpty) {
      val total = pfs.reduce((a, b) ⇒ a.orElse(b))
      testProbe.expectMsgPF() {
        case msg if total.isDefinedAt(msg) ⇒
          val index = pfs.indexWhere(pf ⇒ pf.isDefinedAt(msg))
          pfs(index)(msg)
          expectMsgInAnyOrderPF[Out](testProbe, pfs.take(index) ++ pfs.drop(index + 1): _*)
      }
    }
  }

  protected def getRecipe(recipeName: String): Recipe = {
    val rec = TestRecipe.getRecipe(recipeName)
    val sensoryEvents = rec.sensoryEvents.map(event =>
      event.name match {
        case "InitialEvent" => initialEvent.withMaxFiringLimit(1)
        case _ => event
      }
    )
    rec.copy(sensoryEvents = sensoryEvents)
  }

}

class BakerEventsSpec extends BakerRuntimeTestBase {

  import BakerEventsSpec._

  override def actorSystemName = "BakerEventsSpec"

  private val eventReceiveTimeout = 1 seconds

  before {
    resetMocks
    setupMockResponse()

    // Clean inmemory-journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(defaultActorSystem).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

  "Baker" should {

    "notify ProcessCreated/EventReceived/InteractionStarted/InteractionCompleted events with correct timestamps" in {
      val recipeName = "EventReceivedEventRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)
        listenerProbe = TestProbe()
        listenerFunction = (bakerEvent: BakerEvent) => listenerProbe.ref ! bakerEvent
        _ <- baker.registerBakerEventListener(listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        // TODO check the order of the timestamps later
        _ = expectMsgInAnyOrderPF(listenerProbe,
        {case msg@RecipeInstanceCreated(_, `recipeId`, `recipeName`, `recipeInstanceId`) => msg},
        {case msg@EventReceived(_, _, _, `recipeInstanceId`, Some("someId"), EventInstance("InitialEvent", ingredients)) if ingredients == Map("initialIngredient" -> PrimitiveValue(`initialIngredientValue`)) => msg},
        {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "SieveInteraction") => msg},
        {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "InteractionOne") => msg},
        {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "InteractionTwo") => msg},
        {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "InteractionThree") => msg},
        {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "ProvidesNothingInteraction") => msg},
        {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "InteractionOne", Some(EventInstance("InteractionOneSuccessful", ingredients))) if ingredients == Map("interactionOneIngredient" -> PrimitiveValue("interactionOneIngredient")) => msg},
        {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "InteractionTwo", Some(EventInstance("EventFromInteractionTwo", ingredients))) if ingredients == Map("interactionTwoIngredient" -> PrimitiveValue("interactionTwoIngredient")) => msg},
        {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "InteractionThree", Some(EventInstance("InteractionThreeSuccessful", ingredients))) if ingredients == Map("interactionThreeIngredient" -> PrimitiveValue("interactionThreeIngredient")) => msg},
        {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "ProvidesNothingInteraction", None) => msg},
        {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "SieveInteraction", Some(EventInstance("SieveInteractionSuccessful", ingredients))) if ingredients == Map("sievedIngredient" -> PrimitiveValue("sievedIngredient")) => msg}
        )
        _ = listenerProbe.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with InvalidEvent reason" in {
      val recipeName = "EventRejectedEventRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)
        listenerProbe = TestProbe()
        listenerFunction = (bakerEvent: BakerEvent) => listenerProbe.ref ! bakerEvent
        _ <- baker.registerBakerEventListener(listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        // We used async function here because ThirdEvent is not part of the recipe and throws exception
        _ = baker.fireEventAndResolveWhenReceived(recipeInstanceId, EventInstance.unsafeFrom(ThirdEvent()), "someId")
        _ = listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), EventInstance("ThirdEvent", ingredients), InvalidEvent) if ingredients.isEmpty => msg
        }
        _ = listenerProbe.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with AlreadyReceived reason" in {
      val recipeName = "AlreadyReceivedRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)
        listenerProbe = TestProbe()
        listenerFunction = (bakerEvent: BakerEvent) => listenerProbe.ref ! bakerEvent
        _ <- baker.registerBakerEventListener(listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId") // Same correlationId cannot be used twice
        _ = listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), EventInstance("InitialEvent", ingredients), AlreadyReceived) if ingredients == Map("initialIngredient" -> PrimitiveValue(`initialIngredientValue`)) => msg
        }
        _ = listenerProbe.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with FiringLimitMet reason" in {
      val recipeName = "FiringLimitMetRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)
        listenerProbe = TestProbe()
        listenerFunction = (bakerEvent: BakerEvent) => listenerProbe.ref ! bakerEvent
        _ <- baker.registerBakerEventListener(listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))) // Firing limit is set to 1 in the recipe
        _ = listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, None, EventInstance("InitialEvent", ingredients), FiringLimitMet) if ingredients == Map("initialIngredient" -> PrimitiveValue(`initialIngredientValue`)) => msg
        }
        _ = listenerProbe.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with ReceivePeriodExpired reason" in {
      val recipeName = "ReceivePeriodExpiredRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(getRecipe(recipeName).withEventReceivePeriod(eventReceiveTimeout), mockImplementations)
        listenerProbe = TestProbe()
        listenerFunction = (bakerEvent: BakerEvent) => listenerProbe.ref ! bakerEvent
        _ <- baker.registerBakerEventListener(listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- Future {
          Thread.sleep(eventReceiveTimeout.toMillis)
        }
        _ = baker.fireEventAndResolveWhenReceived(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        _ = listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), EventInstance("InitialEvent", ingredients), ReceivePeriodExpired) if ingredients == Map("initialIngredient" -> PrimitiveValue(`initialIngredientValue`)) => msg
        }
        _ = listenerProbe.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with NoSuchProcess reason" in {
      val recipeName = "NoSuchProcessRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, _) <- setupBakerWithRecipe(getRecipe(recipeName), mockImplementations)
        listenerProbe = TestProbe()
        listenerFunction = (bakerEvent: BakerEvent) => listenerProbe.ref ! bakerEvent
        _ <- baker.registerBakerEventListener(listenerFunction)
        // Skipped baking the process here, so the process with RecipeInstanceId does not exist
        // use a different RecipeInstanceId and use async function because the sync version throws NoSuchProcessException
        _ = baker.fireEventAndResolveWhenReceived(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        _ = listenerProbe.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), EventInstance("InitialEvent", ingredients), NoSuchProcess) if ingredients == Map("initialIngredient" -> PrimitiveValue(`initialIngredientValue`)) => msg
        }
        _ = listenerProbe.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }
  }
}
