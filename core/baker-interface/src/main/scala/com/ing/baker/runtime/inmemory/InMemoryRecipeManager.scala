package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Ref}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.model.RecipeManager

object InMemoryRecipeManager {

  type Store = Map[String, RecipeRecord]

  def build: IO[InMemoryRecipeManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeManager(_))
}

final class InMemoryRecipeManager(inmem: Ref[IO, InMemoryRecipeManager.Store]) extends RecipeManager[IO] {

  import InMemoryRecipeManager._

  override def store(compiledRecipe: CompiledRecipe, timestamp: Long): IO[Unit] =
    inmem.update(_ + (compiledRecipe.recipeId -> RecipeRecord.of(compiledRecipe, updated = timestamp)))

  override def fetch(recipeId: String): IO[Option[RecipeRecord]] =
    inmem.get.map(_.get(recipeId))

  override def fetchAll: IO[Store] =
    inmem.get
}
