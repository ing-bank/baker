package com.ing.baker.runtime.akka

import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.TestProbe
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.TestRecipe.getRecipe
import com.ing.baker.runtime.common.RecipeInformation
import org.slf4j.LoggerFactory

import scala.language.postfixOps

class BakerInquireSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "BakerInquireSpec"

  val log = LoggerFactory.getLogger(classOf[BakerInquireSpec])


  before {
    resetMocks
    setupMockResponse()

    // Clean inmemory-journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(defaultActorSystem).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

  "Baker" should {

    "return recipe if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnRecipe", false)
        recipe <- baker.getRecipe(recipeId)
      } yield recipe.compiledRecipe.name shouldBe "returnRecipe"
    }

    "return all recipes if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnAllRecipes", false)
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2")))
        recipes <- baker.getAllRecipes
        _ = recipes.size shouldBe 2
        _ = recipes(recipeId).compiledRecipe.name shouldBe "returnAllRecipes"
        _ = recipes(recipeId2).compiledRecipe.name shouldBe "returnAllRecipes2"
      } yield succeed
    }

    "return no errors of a recipe with no errors if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnHealthRecipe", false)
        recipeInformation <- baker.getRecipe(recipeId)
        _ = recipeInformation should have(
          'recipeId (recipeId),
          'errors (Set.empty)
        )
      } yield succeed
    }

    "return no errors of all recipes if none contain errors if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnHealthAllRecipe", false)
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
        recipeInformations <- baker.getAllRecipes
        _ = recipeInformations.size shouldBe 2
        _ = recipeInformations.get(recipeId)
          .map(_ should have(
            'recipeId (recipeId),
            'errors (Set.empty)
          )
        )
        _ = recipeInformations.get(recipeId2)
          .map(_ should have(
            'recipeId (recipeId2),
            'errors (Set.empty)
          )
        )
      } yield succeed
    }
  }
}
