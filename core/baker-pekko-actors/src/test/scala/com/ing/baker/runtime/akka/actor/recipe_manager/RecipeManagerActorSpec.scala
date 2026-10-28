package com.ing.baker.runtime.akka.actor.recipe_manager

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexSpec
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.typesafe.config.{Config, ConfigFactory}
import org.apache.pekko.actor.{ActorRef, ActorSystem}
import org.apache.pekko.pattern.ask
import org.apache.pekko.testkit.TestKit
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike

import java.util.UUID
import scala.concurrent.duration._

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

class RecipeManagerActorSpec extends TestKit(ActorSystem("RecipeManagerActorProtoSpec", ProcessIndexSpec.config)) { this: AsyncWordSpecLike with Matchers =>

  "The recipe manager" should {
    "add a recipe to the list when an AddRecipe message is received" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(TestRecipe.getRecipe("AddRecipeRecipe"))
      val recipeManager: ActorRef = system.actorOf(RecipeManagerActor.props(), s"recipeManager-${UUID.randomUUID().toString}")

      for {
        futureAddResult <- recipeManager.ask(AddRecipe(compiledRecipe))(10 seconds)
        recipeId: String = futureAddResult match {
          case AddRecipeResponse(x) => x
          case _ => fail("Adding recipe failed")
        }
        futureGetResult <- recipeManager.ask(GetRecipe(recipeId))(10 seconds)
        _ = futureGetResult match {
          case RecipeFound(_, _) => succeed
          case NoRecipeFound(_) => fail("Recipe not found")
          case _ => fail("Unknown response received")
        }
      } yield succeed
    }
  }
}
