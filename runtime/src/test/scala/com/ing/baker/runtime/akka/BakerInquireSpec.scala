package com.ing.baker.runtime.akka

import akka.persistence.inmemory.extension.{ InMemoryJournalStorage, StorageExtension }
import akka.testkit.TestProbe
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe.getRecipe
import scala.language.postfixOps

class BakerInquireSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "BakerInquireSpec"

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
        _ = assert(recipeInformation.compiledRecipe.recipeId == recipeId && recipeInformation.errors.isEmpty)
      } yield succeed
    }

    "return no errors of all recipes if none contain errors if asked" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("returnHealthAllRecipe", false)
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
        recipeInformations <- baker.getAllRecipes
        _ = recipeInformations.size shouldBe 2
        _ = recipeInformations.get(recipeId)
          .foreach(r => assert(r.compiledRecipe.recipeId == recipeId && r.errors.isEmpty))
        _ = recipeInformations.get(recipeId2)
          .foreach(r => assert(r.compiledRecipe.recipeId == recipeId2 && r.errors.isEmpty))
      } yield succeed
    }
  }
}
