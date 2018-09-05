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
      baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2")))
      val recipes: Map[String, CompiledRecipe] = baker.getAllRecipes()
      recipes.size shouldBe 2
      recipes(recipeId).name shouldBe "returnAllRecipes"
    }

    "return health of a recipe if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnHealthRecipe", false)
      val recipeHealth: RecipeHealth = baker.getHealthRecipe(recipeId)
      recipeHealth.recipeName shouldBe "returnHealthRecipe"
      recipeHealth.recipeId shouldBe recipeId
      recipeHealth.errors shouldBe empty
    }

    "return health of all recipes if asked" in {
      val (baker, recipeId) = setupBakerWithRecipe("returnHealthAllRecipe", false)
      val recipeId2 = baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
      val recipeHealths: Set[RecipeHealth] = baker.getHealthAllRecipes()
      recipeHealths.size shouldBe 2
      recipeHealths.filter(rh => rh.recipeId equals recipeId).map(rh => {
        rh.recipeName shouldBe "returnHealthAllRecipe"
        rh.recipeId shouldBe recipeId
        rh.errors shouldBe empty
      })
      recipeHealths.filter(rh => rh.recipeId equals recipeId2).map(rh => {
        rh.recipeName shouldBe "returnHealthAllRecipe2"
        rh.recipeId shouldBe recipeId2
        rh.errors shouldBe empty
      })
    }
  }
}
