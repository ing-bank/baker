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
      val recipe: CompiledRecipe = baker.getRecipe(recipeId)
      recipe.name shouldBe "returnRecipe"
    }

    "return all recipes if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnAllRecipes", false)
      val recipeId2 = baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2")))
      val recipes: Map[String, CompiledRecipe] = baker.getAllRecipes()
      recipes.size shouldBe 2
      recipes(recipeId).name shouldBe "returnAllRecipes"
      recipes(recipeId2).name shouldBe "returnAllRecipes2"
    }

    "return health of a recipe if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnHealthRecipe", false)
      val recipeHealth: RecipeHealth = baker.getRecipeHealth(recipeId)
      recipeHealth should have(
        'recipeName ("returnHealthRecipe"),
        'recipeId (recipeId),
        'errors (Set.empty)
      )
    }

    "return health of all recipes if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnHealthAllRecipe", false)
      val recipeId2 = baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
      val recipeHealths: Set[RecipeHealth] = baker.getAllRecipeHealths()
      recipeHealths.size shouldBe 2
      recipeHealths.filter(rh => rh.recipeId == recipeId)
        .map(_ should have(
          'recipeName ("returnHealthAllRecipe"),
          'recipeId (recipeId),
          'errors (Set.empty)
        )
      )
      recipeHealths.filter(rh => rh.recipeId == recipeId2)
        .map(_ should have(
          'recipeName ("returnHealthAllRecipe2"),
          'recipeId (recipeId2),
          'errors (Set.empty)
        )
      )
    }
  }
}
