package com.ing.baker.runtime.actortyped.recipe_manager

import java.util.UUID

import akka.actor.Scheduler
import akka.actor.typed.ActorRef
import akka.event.EventStream
import akka.actor.typed.scaladsl.AskPattern._
import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import org.slf4j.{Logger, LoggerFactory}
import akka.actor.typed.scaladsl.adapter._
import akka.util.Timeout
import com.ing.baker.runtime.core.events.{RecipeAdded => CoreRecipeAdded}
import org.mockito.Matchers.any
import org.mockito.Mockito.verify

import scala.concurrent.{Await, Future}

class RecipeManagerTypedSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "RecipeManagerTypedSpec"

  val log: Logger = LoggerFactory.getLogger(classOf[RecipeManagerTypedSpec])
  implicit val to : Timeout = timeout
  implicit val sch: Scheduler = defaultActorSystem.scheduler

  "The RecipeManagerSpec" should {
    "Add a recipe to the list when a AddRecipe message is received" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(TestRecipe.getRecipe("AddRecipeRecipe"))

      val mockEventStream = mock[EventStream]
      val recipeManager: ActorRef[RecipeManagerTyped.Command] =
        defaultActorSystem.spawn(RecipeManagerTyped.behaviour(mockEventStream), s"recipeManager-${UUID.randomUUID().toString}")

      val futureAddResult: Future[RecipeManagerTyped.Reply] =
        recipeManager ? RecipeManagerTyped.AddRecipe(compiledRecipe)
      val recipeId: String = Await.result(futureAddResult, timeout) match {
        case RecipeManagerTyped.AddRecipeResponse(x) => x
        case _ => fail("Adding recipe failed")
      }

      verify(mockEventStream).publish(any[CoreRecipeAdded])

      val futureGetResult: Future[RecipeManagerTyped.Reply] =
        recipeManager ? RecipeManagerTyped.GetRecipe(recipeId)
      val recievedRecipe = Await.result(futureGetResult, timeout) match {
        case RecipeManagerTyped.RecipeFound(recipe, _) => recipe
        case RecipeManagerTyped.NoRecipeFound(_) => fail("Recipe not found")
        case _ => fail("Unknown response received")
      }

      recievedRecipe shouldBe compiledRecipe
    }
  }

}

