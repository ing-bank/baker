package com.ing.baker.runtime.model.recipeinstance.execution

import cats.Functor
import cats.effect.Concurrent
import cats.effect.concurrent.{Deferred, Ref}
import cats.implicits._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.model.recipeinstance.execution.EventsLobby.{KnownOutcomeEvents, KnownRunningExecutions, Lobby}
import com.ing.baker.runtime.scaladsl.{EventInstance, SensoryEventResult}

/** Used by running recipe instances as a gateway to report results of firing sensory events to the consumers, it
  * enables the original sender to await for an specific intermediary event or to await for all the related events
  * to fire.
  *
  * Keeps track of all the transition execution outcomes cascading from a single sensory event to determine if the cascade
  * is done.
  *
  * @param lobby is a mapping between event names and event result promises that can be awaited for
  * @param knownRunningExecutions memory of the transitions that are currently running and should be awaited for before
  *                               completion.
  * @param knownOutcomeEvents memory of the outcome events from the transitions that have already finished.
  * @param completedPromise promise that can be awaited for of the final result after all the related outcome events
  *                         have been received
  * @tparam F
  */
final class EventsLobby[F[_]] private[recipeinstance](
                                                       lobby: Lobby[F],
                                                       knownRunningExecutions: KnownRunningExecutions[F],
                                                       knownOutcomeEvents: KnownOutcomeEvents[F],
                                                       completedPromise: Deferred[F, SensoryEventResult]
                                                     ) {

  def awaitForEvent(eventName: String)(implicit effect: Concurrent[F]): F[SensoryEventResult] =
    getOrCreateWaitingSpot(eventName).flatMap(_.get)

  def awaitForCompleted(implicit effect: Functor[F]): F[SensoryEventResult] =
    completedPromise.get

  def reportTransitionFinished(outcome: TransitionExecution.Outcome, enabledTransitions: Set[TransitionExecution] = Set.empty, output: Option[EventInstance] = None)(implicit effect: Concurrent[F]): F[Unit] = {

    def resolveEvent(eventName: String): F[Unit] =
      for {
        result <- buildSensoryEventResultFromKnownEvents
        waitingSpot <- getOrCreateWaitingSpot(eventName)
        _ <- waitingSpot.complete(result)
      } yield ()

    def reportComplete: F[Unit] =
      buildSensoryEventResultFromKnownEvents.flatMap(completedPromise.complete)

    def buildSensoryEventResultFromKnownEvents: F[SensoryEventResult] =
      knownOutcomeEvents.get.map { knownEvents =>
        SensoryEventResult(
          SensoryEventStatus.Completed,
          knownEvents.map(_.name),
          knownEvents.flatMap(_.providedIngredients).toMap)
      }

    for {
      runningExecutions <- knownRunningExecutions.updateAndGet(
        running => (running ++ enabledTransitions.map(_.id)) - outcome.transitionExecutionId)
      runningExecutionsLeft = runningExecutions.size
      _ <- output.fold(effect.unit)(event =>
        knownOutcomeEvents.update(_ :+ event) *> resolveEvent(event.name))
      _ <- if (runningExecutionsLeft == 0) reportComplete else effect.unit
    } yield ()
  }

  private def getOrCreateWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] = {

    def createWaitingSpot: F[Deferred[F, SensoryEventResult]] =
      Deferred[F, SensoryEventResult].flatMap(newSpot =>
        lobby.update(_ + (eventName -> newSpot)).as(newSpot))

    for {
      spots <- lobby.get
      spot <- spots.get(eventName).fold(createWaitingSpot)(effect.pure)
    } yield spot
  }
}

object EventsLobby {

  type Lobby[F[_]] = Ref[F, Map[String, Deferred[F, SensoryEventResult]]]

  type KnownRunningExecutions[F[_]] = Ref[F, Set[Long]]

  type KnownOutcomeEvents[F[_]] = Ref[F, Seq[EventInstance]]

  def build[F[_]](implicit effect: Concurrent[F]): F[EventsLobby[F]] = {
    for {
      lobby <- Ref.of[F, Map[String, Deferred[F, SensoryEventResult]]](Map.empty)
      knownRunningExecutions <- Ref.of[F, Set[Long]](Set.empty)
      knownOutcomeEvents <- Ref.of[F, Seq[EventInstance]](Seq.empty)
      completePromise <- Deferred[F, SensoryEventResult]
    } yield new EventsLobby(lobby, knownRunningExecutions, knownOutcomeEvents, completePromise)
  }
}