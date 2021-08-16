package com.ing.baker.runtime.inmemory

import cats.effect.concurrent.Ref
import cats.effect.{IO, Timer}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.model.RecipeManager

object InMemoryRecipeManager {

  type Store = Map[String, RecipeRecord]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeManager(_))
}

final class InMemoryRecipeManager(inmem: Ref[IO, InMemoryRecipeManager.Store])(implicit timer: Timer[IO]) extends RecipeManager[IO] {

  import InMemoryRecipeManager._

  override def store(compiledRecipe: CompiledRecipe, timestamp: Long): IO[Unit] =
    inmem.update(_ + (compiledRecipe.recipeId -> RecipeRecord.of(compiledRecipe, updated = timestamp)))

  override def fetch(recipeId: String): IO[Option[RecipeRecord]] =
    inmem.get.map(_.get(recipeId))

  override def fetchAll: IO[Store] =
    inmem.get
}
