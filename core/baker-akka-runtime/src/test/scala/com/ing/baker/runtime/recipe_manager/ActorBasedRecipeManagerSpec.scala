package com.ing.baker.runtime.recipe_manager

import _root_.akka.actor.ActorSystem
import _root_.akka.testkit.{TestKit, TestProbe}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.AkkaBakerConfig.Timeouts
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.common.RecipeRecord
import org.mockito.Mockito.when
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

import java.util.UUID
import scala.concurrent.duration.DurationInt

class ActorBasedRecipeManagerSpec extends TestKit(ActorSystem("ActorBasedRecipeManagerSpec"))
  with AsyncWordSpecLike
  with Matchers
  with MockitoSugar
  with BeforeAndAfter
  with BeforeAndAfterAll {

  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(system)
  }

  private val timeouts: Timeouts = new Timeouts(100.millis, 100.millis, 100.millis, 100.millis, 100.millis, 100.millis)

  private val mockCompiledRecipe: CompiledRecipe = mock[CompiledRecipe]
  when(mockCompiledRecipe.recipeId).thenReturn("1")
  when(mockCompiledRecipe.name).thenReturn("test recipe")

  private val mockInactiveCompiledRecipe: CompiledRecipe = mock[CompiledRecipe]
  when(mockInactiveCompiledRecipe.recipeId).thenReturn("2")
  when(mockInactiveCompiledRecipe.name).thenReturn("inactive test recipe")

  private val recipeRecord = RecipeRecord.of(recipe = mockCompiledRecipe)

  "ActorBasedRecipeManager" should {

    "add recipe record, cache updated" in {
      val actor = TestProbe()

      val manager = new ActorBasedRecipeManager(actor.ref, timeouts)

      val resultRecipeId = manager.put(recipeRecord)

      actor.expectMsg(AddRecipe(recipeRecord.recipe))
      val id = UUID.randomUUID().toString
      actor.reply(AddRecipeResponse(id))

      for {
        _ <- resultRecipeId.map(_ shouldBe id)
        _ <- manager.get(id).map { result =>
          actor.expectNoMessage() // fetched from cache
          result shouldBe Some(recipeRecord)
        }
      } yield succeed

    }

    "get recipe record, cache updated" in {
      val actor = TestProbe()

      val manager = new ActorBasedRecipeManager(actor.ref, timeouts)

      val id1 = UUID.randomUUID().toString

      val eventualNotFound = manager.get(id1)
      actor.expectMsg(GetRecipe(id1))
      actor.reply(NoRecipeFound(id1))

      val id2 = UUID.randomUUID().toString

      val eventualFound = manager.get(id2)
      actor.expectMsg(GetRecipe(id2))
      actor.reply(RecipeFound(mockCompiledRecipe, timestamp = recipeRecord.updated))

      for {
        _ <- eventualNotFound.map(_ shouldBe (None))
        _ <- eventualFound.map(_ shouldBe Some(recipeRecord))
        _ <- manager.get(id2).map { result =>
          actor.expectNoMessage() // fetched from cache
          result shouldBe Some(recipeRecord)
        }
      } yield succeed
    }

    "get all recipe records, cache updated" in {
      val actor = TestProbe()

      val manager = new ActorBasedRecipeManager(actor.ref, timeouts)

      val eventualAllRecipes = manager.all

      actor.expectMsg(GetAllRecipes)
      actor.reply(AllRecipes(Seq(RecipeInformation(recipeRecord.recipe, timestamp = recipeRecord.updated))))

      for {
        _ <- eventualAllRecipes.map(_ shouldBe Seq(recipeRecord))
        _ <- manager.get(recipeRecord.recipeId).map { result =>
          actor.expectNoMessage() // fetched from cache
          result shouldBe Some(recipeRecord)
        }
      } yield succeed
    }

  }
}
