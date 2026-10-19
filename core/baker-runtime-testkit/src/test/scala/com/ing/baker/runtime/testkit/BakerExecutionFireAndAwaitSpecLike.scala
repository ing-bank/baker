package com.ing.baker.runtime.testkit

import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.{Recipe => CommonRecipe}
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.common.BakerException._
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.ing.baker.types.{PrimitiveValue, Value}
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike

import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration._

trait BakerExecutionFireAndAwaitSpecLike { this: AsyncWordSpecLike with Matchers =>

  final case class SomeNotDefinedEvent(name: String)

  protected def initialIngredientValue: String
  protected def interactionOneIngredientValue: String

  protected def mockImplementations: List[InteractionInstance]

  protected def setupBakerWithRecipe(recipeName: String): Future[(Baker, String)]
  protected def setupBakerWithRecipe(recipe: CommonRecipe, implementations: List[InteractionInstance]): Future[(Baker, String)]

  protected def stubInteractionOneWithDelay(interactionDelay: FiniteDuration): Unit

  // Runtime implementations call the concrete runtime awaitEvent method that can throw TimeoutException.
  protected def awaitEventShouldTimeout(baker: Baker, recipeInstanceId: String, eventName: String, timeout: FiniteDuration): Future[Any]

  "basic Baker execution behaviors" should {

    "bake a process successfully if baking for the first time" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FirstTimeBaking")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        exists <- baker.hasRecipeInstance(id) if exists
      } yield succeed
    }

    "bake a process successfully if baking for the first time with MetaData" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FirstTimeBaking")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id, Map("key" -> "value"))
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetadataName).asMap(classOf[String], classOf[String])
      } yield assert(metaData.containsKey("key") && metaData.get("key") == "value")
    }

    "throw an ProcessAlreadyExistsException if baking a process with the same identifier twice" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("DuplicateIdentifierRecipe")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- recoverToSucceededIf[ProcessAlreadyExistsException] {
          baker.bake(recipeId, id)
        }
      } yield succeed
    }

    "allows adding metadata to an RecipeInstance" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataOne")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.addMetaData(id, Map.apply[String, String]("key" -> "value"))
        _ <- baker.addMetaData(id, Map.apply[String, String]("key2" -> "value2"))
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetadataName).asMap(classOf[String], classOf[String])
      } yield assert(
        metaData.containsKey("key") && metaData.get("key") == "value" &&
          metaData.containsKey("key2") && metaData.get("key2") == "value2")
    }

    "allows updating metadata to an RecipeInstance" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataTwo")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.addMetaData(id, Map.apply[String, String]("key" -> "value"))
        _ <- baker.addMetaData(id, Map.apply[String, String]("key" -> "value2"))
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetadataName).asMap(classOf[String], classOf[String])
      } yield assert(
        metaData.containsKey("key") && metaData.get("key") == "value2")
    }

    "allows empty metadata to an RecipeInstance" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataFour")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.addMetaData(id, Map.empty)
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetadataName).asMap(classOf[String], classOf[String])
      } yield assert(metaData.size() == 0)
    }

    "has no metaData if not given" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataThree")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        ingredients: Map[String, Value] <- baker.getIngredients(id)
      } yield assert(!ingredients.contains(RecipeInstanceMetadataName))
    }

    "throw a NoSuchProcessException" when {
      "requesting the process state for a process that does not exist" in {
        for {
          (baker, _) <- setupBakerWithRecipe("NonExistingProcessTest")
          _ <- recoverToSucceededIf[NoSuchProcessException] {
            baker.getRecipeInstanceState(UUID.randomUUID().toString)
          }
        } yield succeed
      }

      "attempting to fire an event for a process that does not exist" in {
        for {
          (baker, _) <- setupBakerWithRecipe("NonExistingProcessEventTest")
          event = EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.InitialEvent(initialIngredientValue))
          response = baker.fireEvent(UUID.randomUUID().toString, event)
          _ <- recoverToSucceededIf[NoSuchProcessException] {
            response.resolveWhenReceived
          }
          _ <- recoverToSucceededIf[NoSuchProcessException] {
            response.resolveWhenCompleted
          }
        } yield succeed
      }
    }

    "throw a IllegalEventException if the event fired is not a valid sensory event" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("NonExistingProcessEventTest")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        intercepted <- recoverToExceptionIf[IllegalEventException] {
          baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SomeNotDefinedEvent("bla")))
        }
        _ = intercepted.getMessage should startWith("No event with name 'SomeNotDefinedEvent' found in recipe 'NonExistingProcessEventTest")
      } yield succeed
    }

    "deleting an instance with removeFromIndex enabled allows baking with the same instanceId again" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("ExampleRecipe")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        exists <- baker.hasRecipeInstance(id) if exists
        _ <- baker.deleteRecipeInstance(id, removeFromIndex = true)
        exists <- baker.hasRecipeInstance(id) if !exists
        _ <- baker.bake(recipeId, id)
      } yield succeed
    }

    "deleting an instance with removeFromIndex disabled will keep it in the index until it expires" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("ExampleRecipe")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        exists <- baker.hasRecipeInstance(id) if exists
        _ <- baker.deleteRecipeInstance(id, removeFromIndex = false)
        exists <- baker.hasRecipeInstance(id) if exists
        _ <- recoverToSucceededIf[ProcessDeletedException] {
          baker.bake(recipeId, id)
        }
      } yield succeed
    }
  }

  "fire and await behaves correctly" should {

    "acknowledge a sensory event by `fireSensoryEventAndAwaitReceived` and wait for persistence" in {
      val recipe = Recipe("awaitReceivedRecipe")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        interactionDelay = 500.millis
        _ = stubInteractionOneWithDelay(interactionDelay)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        startTime = System.currentTimeMillis()
        status <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.InitialEvent(initialIngredientValue)), Option.apply("correlationId"))
        endTime = System.currentTimeMillis()
        duration = (endTime - startTime).millis

        _ = status shouldBe SensoryEventStatus.Received
        _ = duration should be < interactionDelay

        // Also check that the event is in the list of events, which confirms persistence
        events <- baker.getEventNames(recipeInstanceId)
      } yield events should contain("InitialEvent")
    }

    "wait by `awaitCompleted` for a long-running process to finish" in {
      val recipe = Recipe("awaitCompletedRecipe")
        .withInteraction(interactionOne)
        .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        interactionDelay = 500.millis
        _ = stubInteractionOneWithDelay(interactionDelay)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.InitialEvent(initialIngredientValue)), Option.apply("correlationId"))

        startTime = System.currentTimeMillis()
        status <- baker.awaitCompleted(recipeInstanceId, timeout = 1.seconds)
        endTime = System.currentTimeMillis()
        duration = (endTime - startTime).millis

        _ = status shouldBe SensoryEventStatus.Completed
        _ = duration should be > interactionDelay

        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients should contain("interactionOneOriginalIngredient" -> PrimitiveValue(interactionOneIngredientValue))
    }

    "fail `awaitEvent` for non-existent event name" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)

        _ <- recoverToSucceededIf[IllegalEventException] {
          baker.awaitEvent(recipeInstanceId, "ThisEventDoesNotExist", timeout = 1.second)
        }
      } yield succeed
    }

    "return immediately from `awaitCompleted` when the process is already idle" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("awaitCompletedAlreadyIdleRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        status <- baker.awaitCompleted(recipeInstanceId, timeout = 1.seconds)
      } yield status shouldBe SensoryEventStatus.Completed
    }

    "time out from `awaitCompleted` if the process never becomes idle" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("SlowInteraction")
        interactionDelay = 20.seconds
        _ = stubInteractionOneWithDelay(interactionDelay)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.InitialEvent(initialIngredientValue)), Option.apply("correlationId"))
        _ <- recoverToSucceededIf[BakerException.TimeoutException] {
          baker.awaitCompleted(recipeInstanceId, timeout = 1.seconds)
        }
      } yield succeed
    }

    "wait by `awaitEvent` for a specific event to be fired" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.InitialEvent(initialIngredientValue)), Option.apply("correlationId"))
        _ <- baker.awaitEvent(recipeInstanceId, "InteractionThreeSuccessful", timeout = 1.seconds)
        events <- baker.getEventNames(recipeInstanceId)
      } yield events should contain("InteractionThreeSuccessful")
    }

    "return immediately from `awaitEvent` if the event is already present" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.InitialEvent(initialIngredientValue)), Option.apply("correlationId"))
        _ <- baker.awaitEvent(recipeInstanceId, "InitialEvent", timeout = 1.seconds)
        _ <- baker.awaitEvent(recipeInstanceId, "SieveInteractionSuccessful", timeout = 1.seconds)
      } yield succeed
    }

    "time out from `awaitEvent` if the event is never fired" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- recoverToSucceededIf[BakerException.TimeoutException] {
          awaitEventShouldTimeout(baker, recipeInstanceId, "SieveInteractionSuccessful", timeout = 1.seconds)
        }
      } yield succeed
    }

    "fire and await behaves as expected with timerInteraction" should {
      "wait by `awaitCompleted` for a delayed process to finish" in {
        val recipeWithTimer = Recipe("TimerRecipeIdle")
          .withSensoryEvent(delayedEvent)
          .withInteraction(timerInteraction.withOverriddenIngredientName("WaitTime", "waitTime"))

        for {
          (baker, recipeId) <- setupBakerWithRecipe(recipeWithTimer, mockImplementations)
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          delay = 500.millis
          _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.DelayedEvent(delay)), Option.empty)

          startTime = System.currentTimeMillis()
          status <- baker.awaitCompleted(recipeInstanceId, timeout = 5.seconds)
          endTime = System.currentTimeMillis()
          duration = (endTime - startTime).millis

          _ = status shouldBe SensoryEventStatus.Completed
          _ = duration should be > delay
          events <- baker.getEventNames(recipeInstanceId)
        } yield events should contain("TimeWaited")
      }

      "wait by `awaitEvent` for a delayed event (TimeWaited) to be fired" in {
        val recipeWithTimer = Recipe("TimerRecipeEvent")
          .withSensoryEvent(delayedEvent)
          .withInteraction(timerInteraction.withOverriddenIngredientName("WaitTime", "waitTime"))

        for {
          (baker, recipeId) <- setupBakerWithRecipe(recipeWithTimer, mockImplementations)
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          delay = 500.millis
          _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.unsafeFrom(com.ing.baker.recipe.TestRecipe.DelayedEvent(delay)), Option.empty)

          startTime = System.currentTimeMillis()
          _ <- baker.awaitEvent(recipeInstanceId, "TimeWaited", timeout = 5.seconds)
          endTime = System.currentTimeMillis()
          duration = (endTime - startTime).millis

          _ = duration should be > delay
          events <- baker.getEventNames(recipeInstanceId)
        } yield events should contain("TimeWaited")
      }
    }
  }
}







