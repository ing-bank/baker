package com.ing.baker.runtime.actor.recipe_manager

import java.util.UUID

import akka.actor.ActorRef
import akka.pattern.ask
import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.typesafe.config.{Config, ConfigFactory}
import org.slf4j.LoggerFactory

import scala.concurrent.Await

object RecipeManagerSpec {
  val config: Config = ConfigFactory.parseString(
    """
      |akka.persistence.journal.plugin = "inmemory-journal"
      |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |akka.test.timefactor = 3.0
    """.stripMargin)
}

class RecipeManagerSpec  extends BakerRuntimeTestBase {

  override def actorSystemName = "RecipeManagerSpec"

  val log = LoggerFactory.getLogger(classOf[RecipeManagerSpec])

  "The RecipeManagerSpec" should {
    "Add a recipe to the list when a AddRecipe message is received" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(TestRecipe.getRecipe("AddRecipeRecipe"))
      val recipeManager: ActorRef = defaultActorSystem.actorOf(RecipeManager.props(),  s"recipeManager-${UUID.randomUUID().toString}")

      val futureAddResult = recipeManager.ask(AddRecipe(compiledRecipe))(timeout)
      val recipeId: String = Await.result(futureAddResult, timeout) match {
        case AddRecipeResponse(x) => x
        case _ => fail("Adding recipe failed")
      }

      val futureGetResult = recipeManager.ask(GetRecipe(recipeId))(timeout)
      Await.result(futureGetResult, timeout) match {
        case RecipeFound(recipe, _) => recipe
        case NoRecipeFound(_) => fail("Recipe not found")
        case _ => fail("Unknown response received")
      }
    }
  }

}
