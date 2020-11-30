package com.ing.baker.runtime.inmemory

import cats.effect.concurrent.Ref
import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.model.{BakerComponents, RecipeInstanceManager}
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata

object InMemoryRecipeInstanceManager {

  type Store = Map[String, RecipeInstanceStatus[IO]]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeInstanceManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeInstanceManager(_))
}

final class InMemoryRecipeInstanceManager(inmem: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Timer[IO]) extends RecipeInstanceManager[IO] {

  override def fetch(recipeInstanceId: String): IO[Option[RecipeInstanceStatus[IO]]] =
    inmem.get.map(_.get(recipeInstanceId))

  override def store(newRecipeInstance: RecipeInstance[IO])(implicit components: BakerComponents[IO]): IO[Unit] =
    inmem.update(_ + (newRecipeInstance.recipeInstanceId -> RecipeInstanceStatus.Active(newRecipeInstance)))

  override def idleStop(recipeInstanceId: String): IO[Unit] =
    IO.unit

  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] =
    inmem.get.flatMap(_.toList.traverse {
      case (recipeInstanceId, RecipeInstanceStatus.Active(recipeInstance)) =>
        recipeInstance.state.get.map(currentState => RecipeInstanceMetadata(currentState.recipe.recipeId, recipeInstanceId, currentState.createdOn))
      case (recipeInstanceId, RecipeInstanceStatus.Deleted(recipeId, createdOn, _)) =>
        IO.pure(RecipeInstanceMetadata(recipeId, recipeInstanceId, createdOn))
    }).map(_.toSet)

  override protected def fetchAll: IO[Map[String, RecipeInstanceStatus[IO]]] =
    inmem.get

  override protected def remove(recipeInstanceId: String): IO[Unit] =
    inmem.update(_ - recipeInstanceId)
}
