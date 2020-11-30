package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Timer}
import cats.effect.concurrent.Ref
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.model.{BakerComponents, RecipeManager}
import com.ing.baker.runtime.scaladsl.RecipeAdded

import scala.concurrent.duration

object InMemoryRecipeManager {

  type Store = Map[String, (CompiledRecipe, Long)]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeManager(_))
}

final class InMemoryRecipeManager(inmem: Ref[IO, InMemoryRecipeManager.Store])(implicit timer: Timer[IO]) extends RecipeManager[IO] {

  override def store(compiledRecipe: CompiledRecipe, timestamp: Long): IO[Unit] =
    inmem.update(_ + (compiledRecipe.recipeId -> (compiledRecipe, timestamp)))

  override def fetch(recipeId: String): IO[Option[(CompiledRecipe, Long)]] =
    inmem.get.map(_.get(recipeId))

  override def fetchAll: IO[Map[String, (CompiledRecipe, Long)]] =
    inmem.get
}
