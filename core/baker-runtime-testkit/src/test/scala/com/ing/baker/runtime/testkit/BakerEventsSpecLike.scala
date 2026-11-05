package com.ing.baker.runtime.testkit

import com.ing.baker.il.RecipeVisualizer.logger
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl.{CheckPointEvent, Event, Recipe}
import com.ing.baker.runtime.BakerRuntimeTestBase
import com.ing.baker.runtime.common.RejectReason.{AlreadyReceived, FiringLimitMet, InvalidEvent, NoSuchProcess, ReceivePeriodExpired}
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventFired, EventInstance, EventReceived, EventRejected, InteractionCompleted, InteractionStarted, RecipeInstanceCreated}
import com.ing.baker.runtime.testkit.BakerEventsSpecLike.BakerEventCollector
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike

import java.util.UUID
import java.util.concurrent.{LinkedBlockingQueue, TimeUnit}
import scala.concurrent.Future
import scala.concurrent.duration._

object BakerEventsSpecLike {
  final class BakerEventCollector(logEvents: Boolean = false) {

    private val receivedEvents = new LinkedBlockingQueue[BakerEvent]()

    val listenerFunction: BakerEvent => Unit = { event =>
      if (logEvents) logger.info("Listener consumed event {}", event)
      receivedEvents.offer(event)
    }

    def expectMsgInAnyOrderPF[Out](timeoutPerMessage: FiniteDuration, pfs: PartialFunction[Any, Out]*): Unit = {
      var remaining = pfs.toVector
      while (remaining.nonEmpty) {
        val expected = remaining.reduce((a, b) => a.orElse(b))
        val message = fishForSpecificMessage(timeoutPerMessage)(expected)
        val index = remaining.indexWhere(_.isDefinedAt(message))
        remaining(index)(message)
        remaining = remaining.patch(index, Nil, 1)
      }
    }

    def fishForSpecificMessage[Out](timeout: FiniteDuration)(pf: PartialFunction[Any, Out]): Out = {
      val deadline = timeout.fromNow
      while (deadline.hasTimeLeft()) {
        val remainingMillis = math.max(1L, deadline.timeLeft.toMillis)
        Option(receivedEvents.poll(remainingMillis, TimeUnit.MILLISECONDS)) match {
          case Some(msg) if pf.isDefinedAt(msg) => return pf(msg)
          case _ =>
        }
      }

      throw new AssertionError(s"Did not receive expected message within $timeout")
    }

    def expectNoMessage(timeout: FiniteDuration): Unit = {
      Option(receivedEvents.poll(timeout.toMillis, TimeUnit.MILLISECONDS)) match {
        case Some(msg) => throw new AssertionError(s"Expected no more messages for $timeout but received: $msg")
        case None =>
      }
    }
  }

  // TODO this is a copy of TestRecipe.getRecipe(..) with 1 difference, there is a limit on the initialEvent, why?
  protected def getRecipe(recipeName: String): Recipe =
    Recipe(recipeName)
      .withInteractions(
        interactionOne
          .withEventOutputTransformer(interactionOneSuccessful, Map("interactionOneOriginalIngredient" -> "interactionOneIngredient"))
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
      .withCheckpointEvent(CheckPointEvent("CheckPointEvent")
        .withRequiredEvents(Event[InteractionOneSuccessful], Event[EventFromInteractionTwo], Event[InteractionThreeSuccessful]))
      .withSensoryEvents(
        initialEvent.withMaxFiringLimit(1),
        initialEventExtendedName,
        secondEvent,
        notUsedSensoryEvent)
}

trait BakerEventsSpecLike extends BakerRuntimeTestBase { this: AsyncWordSpecLike with Matchers =>

  private val eventReceiveTimeout = 1 seconds

  "Baker" should {

    "notify ProcessCreated/EventReceived/InteractionStarted/InteractionCompleted events with correct timestamps" in {
      val recipeName = "EventReceivedEventRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(BakerEventsSpecLike.getRecipe(recipeName), mockImplementations)
        listenerCollector = new BakerEventCollector()
        _ <- baker.registerBakerEventListener(listenerCollector.listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        // TODO check the order of the timestamps later
        _ = listenerCollector.expectMsgInAnyOrderPF(eventReceiveTimeout,
          {case msg@RecipeInstanceCreated(_, `recipeId`, `recipeName`, `recipeInstanceId`) => msg},
          {case msg@EventReceived(_, _, _, `recipeInstanceId`, Some("someId"), "InitialEvent") => msg},
          {case msg@EventFired(_, _, _, `recipeInstanceId`, "InitialEvent") => msg},
          {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "SieveInteraction") => msg},
          {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "InteractionOne") => msg},
          {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "InteractionTwo") => msg},
          {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "InteractionThree") => msg},
          {case msg@InteractionStarted(_, _, _, `recipeInstanceId`, "ProvidesNothingInteraction") => msg},
          {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "InteractionOne", Some("InteractionOneSuccessful")) => msg},
          {case msg@EventFired(_, _, _, `recipeInstanceId`, "InteractionOneSuccessful") => msg},
          {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "InteractionTwo", Some("EventFromInteractionTwo")) => msg},
          {case msg@EventFired(_, _, _, `recipeInstanceId`, "EventFromInteractionTwo") => msg},
          {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "InteractionThree", Some("InteractionThreeSuccessful")) => msg},
          {case msg@EventFired(_, _, _, `recipeInstanceId`, "InteractionThreeSuccessful") => msg},
          {case msg@EventFired(_, _, _, `recipeInstanceId`, "CheckPointEvent") => msg},
          {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "ProvidesNothingInteraction", None) => msg},
          {case msg@InteractionCompleted(_, _, _, _, `recipeInstanceId`, "SieveInteraction", Some("SieveInteractionSuccessful")) => msg},
          {case msg@EventFired(_, _, _, `recipeInstanceId`, "SieveInteractionSuccessful") => msg}
        )
        _ = listenerCollector.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with InvalidEvent reason" in {
      val recipeName = "EventRejectedEventRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(BakerEventsSpecLike.getRecipe(recipeName), mockImplementations)
        listenerCollector = new BakerEventCollector()
        _ <- baker.registerBakerEventListener(listenerCollector.listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        // We used async function here because ThirdEvent is not part of the recipe and throws exception
        _ = baker.fireEventAndResolveWhenReceived(recipeInstanceId, EventInstance.unsafeFrom(ThirdEvent()), "someId")
        _ = listenerCollector.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), "ThirdEvent", InvalidEvent) => msg
        }
        _ = listenerCollector.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with AlreadyReceived reason" in {
      val recipeName = "AlreadyReceivedRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(BakerEventsSpecLike.getRecipe(recipeName), mockImplementations)
        listenerCollector = new BakerEventCollector()
        _ <- baker.registerBakerEventListener(listenerCollector.listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId") // Same correlationId cannot be used twice
        _ = listenerCollector.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), "InitialEvent", AlreadyReceived) => msg
        }
        _ = listenerCollector.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with FiringLimitMet reason" in {
      val recipeName = "FiringLimitMetRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(BakerEventsSpecLike.getRecipe(recipeName), mockImplementations)
        listenerCollector = new BakerEventCollector()
        _ <- baker.registerBakerEventListener(listenerCollector.listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))) // Firing limit is set to 1 in the recipe
        _ = listenerCollector.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, None, "InitialEvent", FiringLimitMet) => msg
        }
        _ = listenerCollector.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with ReceivePeriodExpired reason" in {
      val recipeName = "ReceivePeriodExpiredRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, recipeId) <- setupBakerWithRecipe(BakerEventsSpecLike.getRecipe(recipeName).withEventReceivePeriod(eventReceiveTimeout), mockImplementations)
        listenerCollector = new BakerEventCollector()
        _ <- baker.registerBakerEventListener(listenerCollector.listenerFunction)
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- Future {
          Thread.sleep(eventReceiveTimeout.toMillis)
        }
        _ = baker.fireEventAndResolveWhenReceived(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        _ = listenerCollector.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), "InitialEvent", ReceivePeriodExpired) => msg
        }
        _ = listenerCollector.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }

    "notify EventRejected event with NoSuchProcess reason" in {
      val recipeName = "NoSuchProcessRecipe"
      val recipeInstanceId = UUID.randomUUID().toString
      for {
        (baker, _) <- setupBakerWithRecipe(BakerEventsSpecLike.getRecipe(recipeName), mockImplementations)
        listenerCollector = new BakerEventCollector()
        _ <- baker.registerBakerEventListener(listenerCollector.listenerFunction)
        // Skipped baking the process here, so the process with RecipeInstanceId does not exist
        // use a different RecipeInstanceId and use async function because the sync version throws NoSuchProcessException
        _ = baker.fireEventAndResolveWhenReceived(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)), "someId")
        _ = listenerCollector.fishForSpecificMessage(eventReceiveTimeout) {
          case msg@EventRejected(_, `recipeInstanceId`, Some("someId"), "InitialEvent", NoSuchProcess) => msg
        }
        _ = listenerCollector.expectNoMessage(eventReceiveTimeout)
      } yield succeed
    }
  }
}
