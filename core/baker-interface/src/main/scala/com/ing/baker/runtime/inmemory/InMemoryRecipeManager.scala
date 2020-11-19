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

final class InMemoryRecipeManager(store: Ref[IO, InMemoryRecipeManager.Store])(implicit timer: Timer[IO]) extends RecipeManager[IO] {

  override def addRecipe(compiledRecipe: CompiledRecipe)(implicit components: BakerComponents[IO]): IO[String] =
    findCompiledRecipeId(compiledRecipe).flatMap {
      case Some(recipeId) =>
        IO.pure(recipeId)
      case None =>
        hardAddRecipe(compiledRecipe)
    }

  override def getRecipe(recipeId: String): IO[Option[(CompiledRecipe, Long)]] =
    store.get.map(_.get(recipeId))

  override def getAllRecipes: IO[Map[String, (CompiledRecipe, Long)]] =
    store.get

  private def hardAddRecipe(compiledRecipe: CompiledRecipe)(implicit components: BakerComponents[IO]): IO[String] =
    for {
      timestamp <- timer.clock.realTime(duration.MILLISECONDS)
      recipeId <- store
        .update(_ + (compiledRecipe.recipeId -> (compiledRecipe, timestamp)))
        .as(compiledRecipe.recipeId)
      _ <- components.eventStream.publish(RecipeAdded(compiledRecipe.name, recipeId, timestamp, compiledRecipe))
    } yield recipeId

  private def findCompiledRecipeId(compiledRecipe: CompiledRecipe): IO[Option[String]] =
    store.get.map(_.collectFirst { case (recipeId, (`compiledRecipe`, _)) => recipeId })
}
