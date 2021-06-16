package com.ing.baker.runtime
import com.ing.baker.il.CompiledRecipe

import scala.collection.concurrent.TrieMap
import scala.concurrent.{ExecutionContext, Future}

private class RecipeManagerImpl(implicit val ex: ExecutionContext) extends RecipeManager {
  type Row = (CompiledRecipe, Long)

  val state:TrieMap[String, Row] = TrieMap.empty

  override def put(compiledRecipe: CompiledRecipe, createdTime: Long): Future[String] = {
    state.+=((compiledRecipe.recipeId, (compiledRecipe, createdTime)))
    Future.successful(compiledRecipe.recipeId)
  }

  override def get(recipeId: String): Future[Option[Row]] = {
    Future.successful(state.get(recipeId))
  }

  override def all: Future[Seq[Row]] = {
    Future.successful(state.values.toSeq)
  }
}

object RecipeManagerImpl {
  def pollingAware(implicit ex: ExecutionContext): RecipeManager = new RecipeManagerImpl() with PollingAware
}
