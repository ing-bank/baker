package com.ing.baker.runtime.recipe_manager

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord
import org.scalatest.matchers.must.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

import scala.collection.concurrent.TrieMap
import scala.concurrent.{ExecutionContext, Future}

class PollingAwareSpec extends AsyncWordSpecLike
  with Matchers
  with MockitoSugar
  with BeforeAndAfter
  with BeforeAndAfterAll {

  private[runtime] class RecipeManagerImpl(implicit val ex: ExecutionContext) extends RecipeManager {
    var count: Int = 0

    val state:TrieMap[String, RecipeRecord] = TrieMap.empty

    override def put(recipeRecord: RecipeRecord): Future[String] = {
      count = count + 1
      state.+=((recipeRecord.recipeId, recipeRecord))
      Future.successful(recipeRecord.recipeId)
    }

    override def get(recipeId: String): Future[Option[RecipeRecord]] = {
      Future.successful(state.get(recipeId))
    }

    override def all: Future[Seq[RecipeRecord]] = {
      Future.successful(state.values.toSeq)
    }
  }

  "PollingAware trait" should {

    "Avoids replacing recipes with elder or same creation time" in {
      val manager = new RecipeManagerImpl() with PollingAware

      val recipe = mock[CompiledRecipe]
      val recipe2 = mock[CompiledRecipe]

      val sameTime = System.currentTimeMillis()
      for {
        _ <- manager.put(RecipeRecord.of(recipe, updated = sameTime)) // the first call
        _ <- manager.put(RecipeRecord.of(recipe, updated = sameTime)) // ignored: same as first
        _ <- manager.put(RecipeRecord.of(recipe, updated = sameTime)) // ignored: it even earlier
        _ <- manager.put(RecipeRecord.of(recipe2, updated = sameTime)) // added: new Recipe
        _ <- manager.put(RecipeRecord.of(recipe2, updated = sameTime + 1000)) // update: because time in future
      } yield {
        manager.count mustEqual(2)
      }
    }
  }
}
