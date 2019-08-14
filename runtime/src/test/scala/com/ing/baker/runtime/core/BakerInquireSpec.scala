package com.ing.baker.runtime.core

import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.TestProbe
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.TestRecipe.getRecipe
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
      val (baker, recipeId) = setupBakerWithRecipe("returnRecipe", false)
      val recipe: CompiledRecipe = baker.getRecipe(recipeId).compiledRecipe
      recipe.name shouldBe "returnRecipe"
    }

    "return all recipes if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnAllRecipes", false)
      val recipeId2 = baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2")))
      val recipes: Map[String, RecipeInformation] = baker.getAllRecipes()
      recipes.size shouldBe 2
      recipes(recipeId).compiledRecipe.name shouldBe "returnAllRecipes"
      recipes(recipeId2).compiledRecipe.name shouldBe "returnAllRecipes2"
    }

    "return no errors of a recipe with no errors if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnHealthRecipe", false)
      val recipeInformation: RecipeInformation = baker.getRecipe(recipeId)
      recipeInformation should have(
        'recipeId (recipeId),
        'errors (Set.empty)
      )
    }

    "return no errors of all recipes if none contain errors if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnHealthAllRecipe", false)
      val recipeId2 = baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
      val recipeInformations: Map[String, RecipeInformation] = baker.getAllRecipes()
      recipeInformations.size shouldBe 2
      recipeInformations.get(recipeId)
        .map(_ should have(
          'recipeId (recipeId),
          'errors (Set.empty)
        )
      )
      recipeInformations.get(recipeId2)
        .map(_ should have(
          'recipeId (recipeId2),
          'errors (Set.empty)
        )
      )
    }
  }
}
