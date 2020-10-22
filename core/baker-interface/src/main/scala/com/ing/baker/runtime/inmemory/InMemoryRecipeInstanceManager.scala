package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Timer}
import cats.effect.concurrent.Ref
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.model.RecipeInstanceManager
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance

import scala.concurrent.duration

object InMemoryRecipeInstanceManager {

  type Store = Map[String, RecipeInstanceStatus]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeInstanceManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeInstanceManager(_))
}

final class InMemoryRecipeInstanceManager(store: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Timer[IO]) extends RecipeInstanceManager[IO] {

  def getRecipeInstance(recipeInstanceId: String): IO[Option[RecipeInstanceStatus]] =
    store.get.map(_.get(recipeInstanceId))

  def addNewRecipeInstance(recipeInstanceId: String, recipe: CompiledRecipe): IO[Unit] =
    for {
      timestamp <- timer.clock.realTime(duration.MILLISECONDS)
      newRecipeInstance = RecipeInstance.empty(recipe, recipeInstanceId)
      _ <- store.update(_ + (recipeInstanceId -> RecipeInstanceStatus.Active(newRecipeInstance, timestamp)))
    } yield ()
}
