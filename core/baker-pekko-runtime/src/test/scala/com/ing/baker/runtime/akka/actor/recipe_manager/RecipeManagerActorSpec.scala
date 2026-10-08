package com.ing.baker.runtime.akka.actor.recipe_manager

import java.util.UUID
import org.apache.pekko.actor.ActorRef
import org.apache.pekko.pattern.ask
import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.typesafe.config.{Config, ConfigFactory}

object RecipeManagerActorSpec {
  val config: Config = ConfigFactory.parseString(
    """
      |pekko.persistence.journal.plugin = "inmemory-journal"
      |pekko.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |pekko.persistence.testkit.events.serialize = false
      |pekko.persistence.testkit.snapshots.serialize = false
      |pekko.test.timefactor = 3.0
    """.stripMargin)
}

class RecipeManagerActorSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "RecipeManagerSpec"

  "The recipe manager" should {
    "add a recipe to the list when an AddRecipe message is received" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(TestRecipe.getRecipe("AddRecipeRecipe"))
      val recipeManager: ActorRef = defaultActorSystem.actorOf(RecipeManagerActor.props(), s"recipeManager-${UUID.randomUUID().toString}")

      for {
        futureAddResult <- recipeManager.ask(AddRecipe(compiledRecipe))(timeout)
        recipeId: String = futureAddResult match {
          case AddRecipeResponse(x) => x
          case _ => fail("Adding recipe failed")
        }
        futureGetResult <- recipeManager.ask(GetRecipe(recipeId))(timeout)
        _ = futureGetResult match {
          case RecipeFound(_, _) => succeed
          case NoRecipeFound(_) => fail("Recipe not found")
          case _ => fail("Unknown response received")
        }
      } yield succeed
    }
  }
}
