package com.ing.baker.baas.state

import java.util.UUID

import com.ing.baker.baas.recipe.Events.{ItemsReserved, OrderPlaced}
import com.ing.baker.baas.recipe.Ingredients.{Item, OrderId, ReservedItems}
import com.ing.baker.baas.recipe.ItemReservationRecipe
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.EventInstance
import org.scalatest.Matchers

class StateNodeSpec extends BakeryFunSpec with Matchers {

  val recipe: CompiledRecipe =
    ItemReservationRecipe.compiledRecipe

  val recipeWithBlockingStrategy: CompiledRecipe =
    ItemReservationRecipe.compiledRecipeWithBlockingStrategy

  val OrderPlacedEvent: EventInstance =
    EventInstance.unsafeFrom(
      OrderPlaced(OrderId("order-1"), List(Item("item-1"))
    ))

  val ItemsReservedEvent: EventInstance =
    EventInstance.unsafeFrom(
      ItemsReserved(ReservedItems(
        List(Item("item-1")),
        Array.fill(1)(Byte.MaxValue)
      )))

  describe("Bakery State Node") {

    test("Recipe management") { context =>
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        recipeId <- client.addRecipe(recipe)
        recipeInformation <- client.getRecipe(recipeId)
        noSuchRecipeError <- client
          .getRecipe("non-existent")
          .map(_ => None)
          .recover { case e: BakerException => Some(e) }
        allRecipes <- client.getAllRecipes
      } yield {
        recipeInformation.compiledRecipe shouldBe recipe
        noSuchRecipeError shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
        allRecipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(recipe)
      }
    }

    test("Baker.bake") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        state <- client.getRecipeInstanceState(recipeInstanceId)
        _ <- context.remoteEventListener.verifyNoEventsArrived
      } yield {
        state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    test("Baker.bake (fail with ProcessAlreadyExistsException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        e <- client
          .bake(recipeId, recipeInstanceId)
          .map(_ => None)
          .recover { case e: BakerException => Some(e) }
        state <- client.getRecipeInstanceState(recipeInstanceId)
      } yield {
        e shouldBe Some(BakerException.ProcessAlreadyExistsException(recipeInstanceId))
        state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    test("Baker.bake (fail with NoSuchRecipeException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        e <- client
          .bake("non-existent", recipeInstanceId)
          .map(_ => None)
          .recover { case e: BakerException => Some(e) }
      } yield e shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
    }

    test("Baker.getRecipeInstanceState (fails with NoSuchProcessException)") { context =>
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        e <- client
          .getRecipeInstanceState("non-existent")
          .map(_ => None)
          .recover { case e: BakerException => Some(e) }
      } yield e shouldBe Some(BakerException.NoSuchProcessException("non-existent"))
    }

    test("Baker.fireEventAndResolveWhenReceived") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        status <- client.fireEventAndResolveWhenReceived(recipeInstanceId, OrderPlacedEvent)
      } yield status shouldBe SensoryEventStatus.Received
    }

    test("Baker.fireEventAndResolveWhenCompleted") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        result <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent)
        serverState <- client.getRecipeInstanceState(recipeInstanceId)
        _ <- eventually(context.remoteEventListener.verifyEventsReceived(2))
      } yield {
        result.eventNames shouldBe Seq("OrderPlaced", "ItemsReserved")
        serverState.events.map(_.name) shouldBe Seq("OrderPlaced", "ItemsReserved")
      }
    }

    test("Baker.fireEventAndResolveWhenCompleted (fails with IllegalEventException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      val event = EventInstance("non-existent", Map.empty)
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        result <- client
          .fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          .map(_ => None)
          .recover { case e: BakerException => Some(e) }
        serverState <- client.getRecipeInstanceState(recipeInstanceId)
        _ <- context.remoteInteraction.didNothing
      } yield {
        result shouldBe Some(BakerException.IllegalEventException("No event with name 'non-existent' found in recipe 'ItemReservation'"))
        serverState.events.map(_.name) should not contain("OrderPlaced")
      }
    }

    test("Baker.fireEventAndResolveOnEvent") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        result <- client.fireEventAndResolveOnEvent(recipeInstanceId, OrderPlacedEvent, "OrderPlaced")
        _ <- eventually {
          for {
            serverState <- client.getRecipeInstanceState(recipeInstanceId)
            _ <- context.remoteEventListener.verifyEventsReceived(2)
          } yield serverState.events.map(_.name) shouldBe Seq("OrderPlaced", "ItemsReserved")
        }
      } yield result.eventNames shouldBe Seq("OrderPlaced")
    }

    test("Baker.getAllRecipeInstancesMetadata") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        clientMetadata <- client.getAllRecipeInstancesMetadata
        serverMetadata <- client.getAllRecipeInstancesMetadata
      } yield clientMetadata shouldBe serverMetadata
    }

    test("Baker.getVisualState") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        _ <- client.getVisualState(recipeInstanceId)
      } yield succeed
    }

    test("Baker.retryInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        recipeId <- client.addRecipe(recipeWithBlockingStrategy)
        _ <- client.bake(recipeId, recipeInstanceId)
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent)
        state1 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- client.retryInteraction(recipeInstanceId, "ReserveItems")
        state2 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
        _ <- context.remoteEventListener.verifyEventsReceived(2)
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain("ItemsReserved")
        state2 should contain("OrderPlaced")
        state2 should contain("ItemsReserved")
      }
    }

    test("Baker.resolveInteraction") { context =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val resolutionEvent = EventInstance.unsafeFrom(
          ItemsReserved(reservedItems = ReservedItems(items = List(Item("resolution-item")), data = Array.empty))
        )
        for {
          _ <- context.remoteComponents.registerToTheCluster
          client <- context.bakeryBoots()
          recipeId <- client.addRecipe(recipeWithBlockingStrategy)
          _ <- client.bake(recipeId, recipeInstanceId)
          _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
          _ <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent)
          state1 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
          _ <- client.resolveInteraction(recipeInstanceId, "ReserveItems", resolutionEvent)
          state2data <- client.getRecipeInstanceState(recipeInstanceId)
          state2 = state2data.events.map(_.name)
          eventState = state2data.ingredients.get("reservedItems").map(_.as[ReservedItems].items.head.itemId)
          // TODO Currently the event listener receives the OrderPlaced... shouldn't also receive the resolved event?
          _ <- context.remoteEventListener.verifyEventsReceived(1)
        } yield {
          state1 should contain("OrderPlaced")
          state1 should not contain("ItemsReserved")
          state2 should contain("OrderPlaced")
          state2 should contain("ItemsReserved")
          eventState shouldBe Some("resolution-item")
        }
    }

    test("Baker.stopRetryingInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteComponents.registerToTheCluster
        client <- context.bakeryBoots()
        recipeId <- client.addRecipe(recipe)
        _ <- client.bake(recipeId, recipeInstanceId)
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- client.fireEventAndResolveWhenReceived(recipeInstanceId, OrderPlacedEvent)
        state1 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
        _ <- client.stopRetryingInteraction(recipeInstanceId, "ReserveItems")
        state2data <- client.getRecipeInstanceState(recipeInstanceId)
        state2 = state2data.events.map(_.name)
        _ <- context.remoteEventListener.verifyEventsReceived(1)
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain("ItemsReserved")
        state2 should contain("OrderPlaced")
        state2 should not contain("ItemsReserved")
      }
    }
  }
}

