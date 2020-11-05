package com.ing.baker.runtime.model.recipeinstance

import cats.Functor
import cats.effect.Concurrent
import cats.effect.concurrent.{Deferred, Ref}
import cats.implicits._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.SensoryEventResult

final class EventsLobby[F[_]](lobby: Ref[F, Map[String, Deferred[F, SensoryEventResult]]], completed: Deferred[F, RecipeInstance]) {

  def awaitForEvent(eventName: String)(implicit effect: Concurrent[F]): F[SensoryEventResult] =
    getOrCreateWaitingSpot(eventName).flatMap(_.get)

  def awaitForCompleted(implicit effect: Functor[F]): F[SensoryEventResult] =
    completed.get.map(recipeInstanceToEventResult)

  def resolveWith(eventName: String, recipeInstance: RecipeInstance)(implicit effect: Concurrent[F]): F[Unit] =
    resolveEvent(eventName, recipeInstanceToEventResult(recipeInstance))

  def reportComplete(recipeInstance: RecipeInstance): F[Unit] =
    completed.complete(recipeInstance)

  private def resolveEvent(eventName: String, sensoryEventResult: SensoryEventResult)(implicit effect: Concurrent[F]): F[Unit] =
    getOrCreateWaitingSpot(eventName).flatMap(_.complete(sensoryEventResult))

  private def getOrCreateWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] =
    for {
      spots <- lobby.get
      spot <- spots.get(eventName)
        .fold(createWaitingSpot(eventName))(effect.pure)
    } yield spot

  private def createWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] =
    Deferred[F, SensoryEventResult].flatMap(newSpot =>
      lobby.update(_ + (eventName -> newSpot)).as(newSpot))

  private def recipeInstanceToEventResult(recipeInstance: RecipeInstance): SensoryEventResult =
    SensoryEventResult(
      sensoryEventStatus = SensoryEventStatus.Completed,
      eventNames = recipeInstance.events.map(_.name),
      ingredients = recipeInstance.ingredients
    )
}

object EventsLobby {

  def build[F[_]](implicit effect: Concurrent[F]): F[EventsLobby[F]] = {
    for {
      lobby <- Ref.of[F, Map[String, Deferred[F, SensoryEventResult]]](Map.empty)
      completeFuture <- Deferred[F, RecipeInstance]
    } yield new EventsLobby(lobby, completeFuture)
  }
}