package com.ing.baker.runtime.akka

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.typesafe.config.ConfigFactory
import org.scalatest.BeforeAndAfterAll
import org.scalatest.flatspec.AsyncFlatSpecLike
import org.scalatest.matchers.should.Matchers

import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration._

/**
 * Test for the awaitCompleted race condition bug.
 *
 * The bug: awaitCompleted() can return before interaction output events (EventTransitions)
 * are fully processed, causing incomplete recipe instance state.
 *
 * This test replicates the exact pattern from WebshopRecipeSpec that reliably triggers
 * the race condition:
 * 1. Fire OrderPlaced event (provides orderId and items ingredients)
 * 2. Fire PaymentMade event (triggers the ReserveItems interaction)
 * 3. ReserveItems interaction runs and produces ItemsReserved output event
 * 4. awaitCompleted() is called
 * 5. State is checked for reservedItems ingredient from the output event
 *
 * Without the fix: Race condition causes awaitCompleted() to return before
 * the ItemsReserved EventTransition completes, so reservedItems is missing.
 *
 * With the fix: awaitCompleted() waits for in-flight EventTransitions to complete.
 */
class AwaitCompletedRaceConditionSpec
    extends TestKit(ActorSystem("AwaitCompletedRaceConditionSpec", ConfigFactory.load()))
    with Matchers
    with AsyncFlatSpecLike
    with BeforeAndAfterAll {

  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(system)
  }

  // === Case classes for events (using reflection-based Event[T] syntax) ===
  
  case class OrderPlaced(orderId: String, items: List[String])
  case class PaymentMade()
  
  // Output events from interaction
  sealed trait ReserveItemsOutput
  case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

  // Interaction definition using reflection-based Event[T] syntax
  val reserveItemsInteraction: Interaction = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
      Ingredient[String]("orderId"),
      Ingredient[List[String]]("items")
    ),
    output = Seq(
      Event[ItemsReserved]
    )
  )

  // Interaction implementation trait - name must match Interaction name exactly
  trait ReserveItems {
    def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput]
  }

  // Recipe using reflection-based Event[T] syntax (matches SimpleWebshopRecipeReflection pattern)
  val recipe: Recipe = Recipe("AwaitCompletedRaceConditionRecipe")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[PaymentMade]
    )
    .withInteraction(
      reserveItemsInteraction
        .withRequiredEvent(Event[PaymentMade])
    )

  // === Test Implementation ===

  class ReserveItemsImpl extends ReserveItems {
    override def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput] = {
      // Return immediately - no artificial delay needed
      // The race condition is in the async event processing, not the interaction itself
      Future.successful(ItemsReserved(items))
    }
  }

  "awaitCompleted" should "wait for interaction output events (EventTransitions) to complete" in {
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new ReserveItemsImpl)
    val baker: Baker = AkkaBaker.localDefault(system, CachingInteractionManager(reserveItemsInstance))

    val compiled = RecipeCompiler.compileRecipe(recipe)
    val recipeInstanceId = UUID.randomUUID().toString

    val testOrderId = "order-id"
    val testItems = List("item1", "item2")

    val orderPlaced = EventInstance.unsafeFrom(OrderPlaced(testOrderId, testItems))
    val paymentMade = EventInstance.unsafeFrom(PaymentMade())

    for {
      recipeId <- baker.addRecipe(RecipeRecord.of(compiled))
      _ <- baker.bake(recipeId, recipeInstanceId)
      // Fire OrderPlaced - provides ingredients but doesn't trigger interaction yet
      _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, orderPlaced)
      // Fire PaymentMade - this triggers the ReserveItems interaction
      _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, paymentMade)
      // awaitCompleted should wait for the ItemsReserved EventTransition to finish
      _ <- baker.awaitCompleted(recipeInstanceId, timeout = 5.seconds)
      // Get state AFTER awaitCompleted returns
      state <- baker.getRecipeInstanceState(recipeInstanceId)
    } yield {
      // The reservedItems ingredient from ItemsReserved event MUST be present
      // Without the fix, this fails because awaitCompleted returns too early
      val provided = state
        .ingredients
        .find(_._1 == "reservedItems")
        .map(_._2.as[List[String]])
        .map(_.mkString(", "))
        .getOrElse("No reserved items")

      provided shouldBe testItems.mkString(", ")
    }
  }

  it should "consistently have reservedItems after awaitCompleted (stress test)" in {
    // Run multiple iterations to catch the race condition
    val iterations = 20

    Future.sequence((1 to iterations).map { i =>
      val reserveItemsInstance = InteractionInstance.unsafeFrom(new ReserveItemsImpl)
      val baker: Baker = AkkaBaker.localDefault(system, CachingInteractionManager(reserveItemsInstance))

      val compiled = RecipeCompiler.compileRecipe(recipe)
      val recipeInstanceId = UUID.randomUUID().toString

      val testOrderId = s"order-$i"
      val testItems = List(s"item1-$i", s"item2-$i")

      val orderPlaced = EventInstance.unsafeFrom(OrderPlaced(testOrderId, testItems))
      val paymentMade = EventInstance.unsafeFrom(PaymentMade())

      for {
        recipeId <- baker.addRecipe(RecipeRecord.of(compiled))
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, orderPlaced)
        _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, paymentMade)
        _ <- baker.awaitCompleted(recipeInstanceId, timeout = 5.seconds)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield {
        val hasReservedItems = state.ingredients.contains("reservedItems")
        val hasEvent = state.eventNames.contains("ItemsReserved")
        (i, hasReservedItems && hasEvent, state.ingredients.keys.toList, state.eventNames)
      }
    }).map { results =>
      val failures = results.filterNot(_._2)

      if (failures.nonEmpty) {
        failures.foreach { case (i, _, ingredients, events) =>
          info(s"Iteration $i failed: ingredients=$ingredients, events=$events")
        }
      }

      // All iterations should have reservedItems present
      // Without the fix, some iterations will fail due to the race condition
      failures shouldBe empty

      info(s"All $iterations iterations completed successfully with reservedItems present")
      succeed
    }
  }
}
