package com.ing.baker.runtime.model.recipeinstance

import cats.implicits._
import cats.effect.{Concurrent, Sync}
import cats.effect.concurrent.{Deferred, Ref}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.SensoryEventResult

final class EventsLobby[F[_]](lobby: Ref[F, Map[String, Deferred[F, SensoryEventResult]]]) {

  def awaitForEvent(eventName: String)(implicit effect: Concurrent[F]): F[SensoryEventResult] =
    getOrCreateWaitingSpot(eventName).flatMap(_.get)

  def resolveEvent(eventName: String, sensoryEventResult: SensoryEventResult)(implicit effect: Concurrent[F]): F[Unit] =
    getOrCreateWaitingSpot(eventName).flatMap(_.complete(sensoryEventResult))

  def resolveWith(eventName: String, recipeInstance: RecipeInstance)(implicit effect: Concurrent[F]): F[Unit] = {
    val result = SensoryEventResult(
      sensoryEventStatus = SensoryEventStatus.Completed,
      eventNames = recipeInstance.events.map(_.name),
      ingredients = recipeInstance.ingredients
    )
    resolveEvent(eventName, result)
  }

  private def getOrCreateWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] =
    for {
      spots <- lobby.get
      spot <- spots.get(eventName)
        .fold(createWaitingSpot(eventName))(effect.pure)
    } yield spot

  private def createWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] =
    Deferred[F, SensoryEventResult].flatMap(newSpot =>
      lobby.update(_ + (eventName -> newSpot)).as(newSpot))
}

object EventsLobby {

  def build[F[_]](implicit effect: Sync[F]): F[EventsLobby[F]] =
    Ref.of[F, Map[String, Deferred[F, SensoryEventResult]]](Map.empty).map(new EventsLobby(_))
}