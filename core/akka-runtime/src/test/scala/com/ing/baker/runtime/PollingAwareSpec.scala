package com.ing.baker.runtime

import com.ing.baker.il.CompiledRecipe
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatest.matchers.must.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
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

    val state:TrieMap[String, (CompiledRecipe, Long)] = TrieMap.empty

    override def put(compiledRecipe: CompiledRecipe, createdTime: Long): Future[String] = {
      count = count + 1
      state.+=((compiledRecipe.recipeId, (compiledRecipe, createdTime)))
      Future.successful(compiledRecipe.recipeId)
    }

    override def get(recipeId: String): Future[Option[(CompiledRecipe, Long)]] = {
      Future.successful(state.get(recipeId))
    }

    override def all: Future[Seq[(CompiledRecipe, Long)]] = {
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
        _ <- manager.put(recipe, sameTime) // the first call
        _ <- manager.put(recipe, sameTime) // ignored: same as first
        _ <- manager.put(recipe, sameTime) // ignored: it even earlier
        _ <- manager.put(recipe2, sameTime) // added: new Recipe
        _ <- manager.put(recipe2, sameTime + 1000) // update: because time in future
      } yield {
        manager.count mustEqual(2)
      }
    }
  }
}
