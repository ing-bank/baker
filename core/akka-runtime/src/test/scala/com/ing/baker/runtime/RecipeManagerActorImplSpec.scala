package com.ing.baker.runtime

import _root_.akka.actor.ActorSystem
import _root_.akka.testkit.{TestKit, TestProbe}
import _root_.akka.util.Timeout
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

import java.util.UUID
import java.util.concurrent.TimeUnit

class RecipeManagerActorImplSpec extends TestKit(ActorSystem("MySpec"))
  with AsyncWordSpecLike
  with Matchers
  with MockitoSugar
  with BeforeAndAfter
  with BeforeAndAfterAll {
  private val timeout: Timeout = Timeout(5, TimeUnit.SECONDS)
  private val settings: RecipeManagerActorImpl.Settings = RecipeManagerActorImpl.Settings(timeout, timeout)


  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(system)
  }

  "RecipeManagerActorImpl" should {

    "implement add" in {
      val actor = TestProbe()

      val manager = new RecipeManagerActorImpl(actor.ref, settings)
      val recipe = mock[CompiledRecipe]

      val eventualString = manager.put(recipe)
      actor.expectMsg(AddRecipe(recipe))
      val id = UUID.randomUUID().toString

      actor.reply(AddRecipeResponse(id))
      eventualString.map(_ shouldBe id)
    }

    "implement get" in {
      val actor = TestProbe()

      val manager = new RecipeManagerActorImpl(actor.ref, settings)
      val recipe = mock[CompiledRecipe]

      val id1 = UUID.randomUUID().toString

      val eventualNotFound = manager.get(id1)
      actor.expectMsg(GetRecipe(id1))

      actor.reply(NoRecipeFound(id1))

      val id2 = UUID.randomUUID().toString

      val eventualFound = manager.get(id2)
      actor.expectMsg(GetRecipe(id2))
      val compiledRecipe = mock[CompiledRecipe]
      val timestamp = 42l
      actor.reply(RecipeFound(compiledRecipe, timestamp))

      for {
        _ <- eventualNotFound.map(_ shouldBe(None))
        _ <- eventualFound.map(_.get._1.shouldBe(compiledRecipe))
      } yield succeed
    }

    "implement getAll" in {
      val actor = TestProbe()

      val manager = new RecipeManagerActorImpl(actor.ref, settings)
      val recipe = mock[CompiledRecipe]

      val eventualString = manager.all
      actor.expectMsg(GetAllRecipes)

      val timestamp = 42l

      actor.reply(AllRecipes(Seq(RecipeInformation(recipe, timestamp))))
      eventualString.map(_ shouldBe Seq((recipe, timestamp)))
    }
  }
}
