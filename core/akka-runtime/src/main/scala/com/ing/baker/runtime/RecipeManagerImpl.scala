package com.ing.baker.runtime
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord

import scala.collection.concurrent.TrieMap
import scala.concurrent.{ExecutionContext, Future}

private class RecipeManagerImpl(implicit val ex: ExecutionContext) extends RecipeManager {

  val state:TrieMap[String, RecipeRecord] = TrieMap.empty


  override def put(recipeRecord: RecipeRecord): Future[String] = {
    state. += ((recipeRecord.recipeId,recipeRecord))
    Future.successful(recipeRecord.recipeId)
  }

  override def get(recipeId: String): Future[Option[RecipeRecord]] = {
    Future.successful(state.get(recipeId))
  }

  override def all: Future[Seq[RecipeRecord]] = {
    Future.successful(state.values.toSeq)
  }
}

object RecipeManagerImpl {
  def pollingAware(implicit ex: ExecutionContext): RecipeManager = new RecipeManagerImpl() with PollingAware
}
