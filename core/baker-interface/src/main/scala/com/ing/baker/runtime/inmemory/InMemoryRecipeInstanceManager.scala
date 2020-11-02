package com.ing.baker.runtime.inmemory

import cats.effect.concurrent.Ref
import cats.effect.{IO, Timer}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.model.RecipeInstanceManager
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata

import scala.concurrent.duration

object InMemoryRecipeInstanceManager {

  type Store = Map[String, RecipeInstanceStatus]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeInstanceManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeInstanceManager(_))
}

final class InMemoryRecipeInstanceManager(store: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Timer[IO]) extends RecipeInstanceManager[IO] {

  override def get(recipeInstanceId: String): IO[Option[RecipeInstanceStatus]] =
    store.get.map(_.get(recipeInstanceId))

  override def add(recipeInstanceId: String, recipe: CompiledRecipe): IO[Unit] =
    for {
      timestamp <- timer.clock.realTime(duration.MILLISECONDS)
      newRecipeInstance = RecipeInstance.empty(recipe, recipeInstanceId, timestamp)
      _ <- store.update(_ + (recipeInstanceId -> RecipeInstanceStatus.Active(newRecipeInstance)))
    } yield ()

  override def update(recipeInstanceId: String, updateFunction: RecipeInstance => RecipeInstance): IO[RecipeInstance] =
    for {
      storeMap <- store.updateAndGet { storeMap =>
        storeMap.get(recipeInstanceId) match {
          case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
            storeMap + (recipeInstanceId -> RecipeInstanceStatus.Active(updateFunction(recipeInstance)))
          case _ =>
            storeMap
        }
      }
      recipeInstance <- storeMap.get(recipeInstanceId) match {
        case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
          IO.pure(recipeInstance)
        case _ =>
          IO.raiseError(new IllegalStateException("""
            |Imminent bug, this state should be unreachable since the update function should exclusively be called
            |within the "fireEvent" implementation of the RecipeInstance, which should exist and active when triggered.
            |""".stripMargin))
      }
    } yield recipeInstance

  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] =
    store.get.map(_.map {
      case (recipeInstanceId, RecipeInstanceStatus.Active(recipeInstance)) =>
        RecipeInstanceMetadata(recipeInstance.recipe.recipeId, recipeInstanceId, recipeInstance.createdOn)
      case (recipeInstanceId, RecipeInstanceStatus.Deleted(recipeId, createdOn, _)) =>
        RecipeInstanceMetadata(recipeId, recipeInstanceId, createdOn)
    }.toSet)
}
