package com.ing.baker.runtime
import com.ing.baker.il.CompiledRecipe

import scala.collection.concurrent.TrieMap
import scala.concurrent.Future

class RecipeManagerImpl extends RecipeManager {
  type Row = (CompiledRecipe, Long)

  val state:TrieMap[String, Row] = TrieMap.empty

  override def add(compiledRecipe: CompiledRecipe): Future[String] = {
    state.+=((compiledRecipe.recipeId, (compiledRecipe, System.currentTimeMillis())))
    Future.successful(compiledRecipe.recipeId)
  }

  override def get(recipeId: String): Future[Option[Row]] = {
    Future.successful(state.get(recipeId))
  }

  override def all(): Future[Seq[Row]] = {
    Future.successful(state.values.toSeq)
  }
}