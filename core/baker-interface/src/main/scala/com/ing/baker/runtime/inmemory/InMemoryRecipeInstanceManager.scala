package com.ing.baker.runtime.inmemory

import cats.implicits._
import cats.effect.concurrent.Ref
import cats.effect.{IO, Timer}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.model.RecipeInstanceManager
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata
import com.ing.baker.runtime.serialization.Encryption

import scala.concurrent.duration._

object InMemoryRecipeInstanceManager {

  type Store = Map[String, RecipeInstanceStatus[IO]]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeInstanceManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeInstanceManager(_))
}

final class InMemoryRecipeInstanceManager(store: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Timer[IO]) extends RecipeInstanceManager[IO] {

  override def get(recipeInstanceId: String): IO[Option[RecipeInstanceStatus[IO]]] =
    store.get.map(_.get(recipeInstanceId))

  override def add(recipeInstanceId: String, recipe: CompiledRecipe): IO[Unit] =
    for {
      // TODO move what is generic back to the RecipeInstanceManager trait and parametrize the recipe settings
      newRecipeInstance <- RecipeInstance.empty[IO](recipe, recipeInstanceId, RecipeInstance.Settings(Some(5.seconds), Encryption.NoEncryption, Seq.empty))
      _ <- store.update(_ + (recipeInstanceId -> RecipeInstanceStatus.Active(newRecipeInstance)))
    } yield ()

  override def update(recipeInstanceId: String, updateFunction: RecipeInstance[IO] => RecipeInstance[IO]): IO[RecipeInstance[IO]] =
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

  override def idleStop(recipeInstanceId: String): IO[Unit] =
    for {
      current <- get(recipeInstanceId)
      timestamp <- timer.clock.realTime(MILLISECONDS)
      _ <- store.update { store =>
        current match {
          case Some(RecipeInstanceStatus.Active(recipeInstance)) =>
            store + (recipeInstanceId -> RecipeInstanceStatus.Deleted(recipeInstance.recipe.recipeId, recipeInstance.createdOn, timestamp))
          case _ =>
            store
        }
      }
    } yield ()

  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] =
    store.get.flatMap(_.toList.traverse {
      case (recipeInstanceId, RecipeInstanceStatus.Active(recipeInstance)) =>
        recipeInstance.state.get.map(currentState => RecipeInstanceMetadata(currentState.recipe.recipeId, recipeInstanceId, currentState.createdOn))
      case (recipeInstanceId, RecipeInstanceStatus.Deleted(recipeId, createdOn, _)) =>
        IO.pure(RecipeInstanceMetadata(recipeId, recipeInstanceId, createdOn))
    }).map(_.toSet)
}
