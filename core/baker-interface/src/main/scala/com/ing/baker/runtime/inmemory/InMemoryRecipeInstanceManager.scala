package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Timer}
import cats.effect.concurrent.Ref
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.inmemory.InMemoryRecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.RecipeInstanceManager
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance

import scala.concurrent.duration

object InMemoryRecipeInstanceManager {

  type Store = Map[String, RecipeInstanceStatus]

  sealed trait RecipeInstanceStatus

  object RecipeInstanceStatus {

    case class Active(recipeInstance: RecipeInstance, createdOn: Long) extends RecipeInstanceStatus

    case class Deleted(createdOn: Long, deletedOn: Long) extends RecipeInstanceStatus
  }

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeInstanceManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeInstanceManager(_))
}

// TODO a lot of this logic can be moved to the more general RecipeInstanceManager[F[_]]
final class InMemoryRecipeInstanceManager(store: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Timer[IO]) extends RecipeInstanceManager[IO] {

  override def bake(recipeInstanceId: String, recipe: CompiledRecipe): IO[RecipeInstanceManager.BakeOutcome] = {
    getRecipeInstance(recipeInstanceId).flatMap {
      case Some(_: RecipeInstanceStatus.Active) =>
        IO.pure(RecipeInstanceManager.BakeOutcome.RecipeInstanceAlreadyExists)
      case Some(_: RecipeInstanceStatus.Deleted) =>
        IO.pure(RecipeInstanceManager.BakeOutcome.RecipeInstanceDeleted)
      case None =>
        addNewRecipeInstance(recipeInstanceId, recipe).as(RecipeInstanceManager.BakeOutcome.Baked)
    }
  }

  private def getRecipeInstance(recipeInstanceId: String): IO[Option[RecipeInstanceStatus]] =
    store.get.map(_.get(recipeInstanceId))

  private def addNewRecipeInstance(recipeInstanceId: String, recipe: CompiledRecipe): IO[Unit] =
    for {
      timestamp <- timer.clock.realTime(duration.MILLISECONDS)
      newRecipeInstance = RecipeInstance.empty(recipe, recipeInstanceId)
      _ <- store.update(_ + (recipeInstanceId -> RecipeInstanceStatus.Active(newRecipeInstance, timestamp)))
    } yield ()
}
