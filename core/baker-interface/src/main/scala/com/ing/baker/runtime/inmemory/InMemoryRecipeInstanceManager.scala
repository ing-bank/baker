package com.ing.baker.runtime.inmemory

import cats.data.EitherT
import cats.effect.{IO, Timer}
import cats.effect.concurrent.Ref
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.model.{BakerComponents, RecipeInstanceManager}
import com.ing.baker.runtime.model.RecipeInstanceManager.{FireOutcome, FireSensoryEventRejection, RecipeInstanceStatus}
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, TransitionExecutionOutcome}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FireTransitionValidation
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceMetadata, SensoryEventResult}

import scala.concurrent.duration

object InMemoryRecipeInstanceManager {

  type Store = Map[String, RecipeInstanceStatus]

  def build(implicit timer: Timer[IO]): IO[InMemoryRecipeInstanceManager] =
    Ref.of[IO, Store](Map.empty).map(new InMemoryRecipeInstanceManager(_))
}

final class InMemoryRecipeInstanceManager(store: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Timer[IO]) extends RecipeInstanceManager[IO] {

  def get(recipeInstanceId: String): IO[Option[RecipeInstanceStatus]] =
    store.get.map(_.get(recipeInstanceId))

  def add(recipeInstanceId: String, recipe: CompiledRecipe): IO[Unit] =
    for {
      timestamp <- timer.clock.realTime(duration.MILLISECONDS)
      newRecipeInstance = RecipeInstance.empty(recipe, recipeInstanceId, timestamp)
      _ <- store.update(_ + (recipeInstanceId -> RecipeInstanceStatus.Active(newRecipeInstance)))
    } yield ()

  def set(recipeInstanceId: String, recipeInstance: RecipeInstance): IO[Unit] =
    for {
      storeMap <- store.get
      _ <- storeMap.get(recipeInstanceId) match {
        case None =>
          IO.raiseError(new IllegalStateException("Tried to update a non-existent recipe instance at the in-memory implementation, this should be unreachable, imminent bug"))
        case Some(RecipeInstanceStatus.Deleted(_, _, _)) =>
          IO.raiseError(new IllegalStateException("Tried to update a deleted recipe instance at the in-memory implementation, this should be unreachable, imminent bug"))
        case Some(RecipeInstanceStatus.Active(_)) =>
          store.update(_ + (recipeInstanceId -> RecipeInstanceStatus.Active(recipeInstance)))
      }
    } yield ()

  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] =
    store.get.map(_.map {
      case (recipeInstanceId, RecipeInstanceStatus.Active(recipeInstance)) =>
        RecipeInstanceMetadata(recipeInstance.recipe.recipeId, recipeInstanceId, recipeInstance.createdOn)
      case (recipeInstanceId, RecipeInstanceStatus.Deleted(recipeId, createdOn, _)) =>
        RecipeInstanceMetadata(recipeId, recipeInstanceId, createdOn)
    }.toSet)

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[IO]): FireOutcome[IO, SensoryEventStatus] = {
    for {
      recipeInstance <- getRecipeInstanceWithRejection(recipeInstanceId)
      newStateAndEffect <- recipeInstance.fire[IO](event, correlationId).leftFlatMap {
        case (rejection, reason) =>
          // TODO log this before, at the recipe instance
          // TODO log reason
          EitherT.pure(rejection)
      }
      (updatedRecipeInstance: RecipeInstance, fireEventEffect: IO[TransitionExecutionOutcome]) = newStateAndEffect
      _ <- EitherT.liftF(set(recipeInstanceId, updatedRecipeInstance))
      _ <- EitherT.liftF(fireEventEffect.runAsync {
        case Left(e) =>
          ???
        case Right(outcome) =>
          ???
      }.toIO)
    } yield SensoryEventStatus.Received
  }

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[IO]): FireOutcome[IO, SensoryEventResult] = ???

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String])(implicit components: BakerComponents[IO]): FireOutcome[IO, SensoryEventResult] = ???

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[IO]): (FireOutcome[IO, SensoryEventStatus], FireOutcome[IO, SensoryEventResult]) = ???

}
