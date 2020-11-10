package com.ing.baker.runtime.model.recipeinstance.modules

import cats.data.EitherT
import cats.effect.concurrent.Ref
import cats.effect.{CancelToken, ConcurrentEffect, IO, Sync, Timer}
import cats.implicits._
import com.ing.baker.il.petrinet.Place
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.{EventsLobby, FailureStrategy, RecipeInstance, TransitionExecution, TransitionExecutionOutcome}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.petrinet.api._
import com.typesafe.scalalogging.Logger

import scala.concurrent.duration._

trait RecipeInstanceExecutionLogic { recipeInstance: RecipeInstance =>

  /** Validates an attempt to fire an event, and if valid, executes the cascading effect of firing the event.
    * The returning effect will resolve right after the event has been recorded, but asynchronously cascades the recipe
    * instance execution semantics.
    *
    * @return either a validation rejection or TODO.
    *         Note that the operation is wrapped within an effect because 2 reasons, first, the validation checks for
    *         current time, and second, if there is a rejection a message is logged, both are suspended into F.
    */
  def fire[F[_]](input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, EventsLobby[F]] =
    for {
      currentTime <- EitherT.liftF(timer.clock.realTime(MILLISECONDS))
      transitionExecution <- logRejectionReasonIfAny(
        recipeInstance.validateExecution(input, correlationId, currentTime))
      eventsLobby <- EitherT.liftF(RecipeInstanceExecutionLogic.base[F](recipeInstanceId, transitionExecution, logger))
    } yield eventsLobby

  /** Helper function to log and remove the textual rejection reason of the `fire` operation. It basically exchanges the
    * String inside the returning `Either` for an external effect `F`.
    *
    * @param validation
    * @param effect
    * @return
    */
  private def logRejectionReasonIfAny[F[_]](validation: Either[(FireSensoryEventRejection, String), TransitionExecution])(implicit effect: Sync[F]): EitherT[F, FireSensoryEventRejection, TransitionExecution] = {
    // TODO relate this to the recipe instance logger
    EitherT(validation match {
      case Left((rejection, reason)) =>
        effect.delay(logger.info(s"Event rejected: $reason"))
          .as(Left(rejection))
      case Right(transitionExecution) =>
        effect.pure(Right(transitionExecution))
    })
  }
}

object RecipeInstanceExecutionLogic {

  type ScheduledRetries[F[_]] = Ref[F, Map[Long, CancelToken[F]]]

  /** Base case of the recipe instance execution semantics.
    *
    * @param recipeInstanceId
    * @param transitionExecution
    * @param logger
    * @param components
    * @param effect
    * @param timer
    * @tparam F
    * @return
    */
  private[modules] def base[F[_]](recipeInstanceId: String, transitionExecution: TransitionExecution, logger: Logger)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): F[EventsLobby[F]] =
    for {
      scheduledRetries <- Ref.of[F, Map[Long, CancelToken[F]]](Map.empty)
      eventsLobby <- EventsLobby.build[F]
      context = new SteppingContext[F](recipeInstanceId, scheduledRetries, eventsLobby, logger)
      _ <- context.step(transitionExecution)
    } yield eventsLobby

  /** TODO rewrite this within the context of 1 event
    * Inductive step of the recipe instance execution semantics.
    * Attempts to progress the execution of the recipe instance from the outcome of a previous execution.
    *
    * This is separated because we must be careful to take only the latest state of the recipe instance by fetching it
    * from the RecipeInstanceManager component, this is because effects are happening asynchronously.
    *
    * Note that the execution effects are still suspended and should be run on due time to move the recipe instance state
    * forward with the resulting TransitionExecutionOutcome.
    *
    * @param components
    * @param effect
    * @param timer
    * @tparam F
    * @return
    */
  private[modules] class SteppingContext[F[_]](recipeInstanceId: String, scheduledRetries: ScheduledRetries[F], eventsLobby: EventsLobby[F], logger: Logger)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]) {

    def step(transitionExecution: TransitionExecution): F[Unit] =
      for {
        _ <- components.recipeInstanceManager.update(recipeInstanceId, _.addExecution(transitionExecution))
        _ <- eventsLobby.reportTransitionStarted(transitionExecution.id)
        _ <- effect.runAsync(transitionExecution.execute)(asyncOutcomeCallback).to[F]
      } yield ()

    private def asyncOutcomeCallback(asyncOutcome: Either[Throwable, TransitionExecutionOutcome]): IO[Unit] =
      effect.toIO(asyncOutcome match {
        case Right(outcome: TransitionExecutionOutcome.Completed) =>
          handleCompletedOutcome(outcome)
        case Right(outcome: TransitionExecutionOutcome.Failed) =>
          outcome.exceptionStrategy match {
            case FailureStrategy.Continue(marking, output) =>
              handleFailureWithContinue(outcome)(marking, output)
            case FailureStrategy.BlockTransition =>
              handleFailureWithBlockTransition(outcome)
            case FailureStrategy.RetryWithDelay(delay) =>
              handleFailureWithRetryWithDelay(outcome)(delay)
          }
        case Left(e) =>
          RecipeInstance.logImpossibleException(logger, e).to[F]
      })

    private def handleCompletedOutcome(outcome: TransitionExecutionOutcome.Completed): F[Unit] =
      for {
        recipeInstance <- components.recipeInstanceManager.update(recipeInstanceId, _.recordExecutionOutcome(outcome))
        _ <- eventsLobby.reportTransitionFinished(outcome.transitionExecutionId, outcome.output)
        enabledExecutions = recipeInstance.allEnabledExecutions
        _ <- enabledExecutions.toList.traverse(step)
      } yield ()

    private def handleFailureWithContinue(outcome: TransitionExecutionOutcome.Failed)(marking: Marking[Place], output: Option[EventInstance]): F[Unit] =
      handleCompletedOutcome(TransitionExecutionOutcome.Completed(
        transitionExecutionId = outcome.transitionExecutionId,
        transitionId = outcome.transitionId,
        correlationId = outcome.correlationId,
        timeStarted = outcome.timeStarted,
        timeCompleted = outcome.timeFailed,
        consumed = outcome.consume,
        produced = marshalMarking(marking),
        output = output))

    private def handleFailureWithBlockTransition(outcome: TransitionExecutionOutcome.Failed): F[Unit] = {
      for {
        _ <- components.recipeInstanceManager.update(recipeInstanceId, _.recordExecutionOutcome(outcome))
        _ <- eventsLobby.reportTransitionFinished(outcome.transitionExecutionId, output = None)
      } yield ()
    }

    private def handleFailureWithRetryWithDelay(outcome: TransitionExecutionOutcome.Failed)(delay: Long): F[Unit] = {
      for {
        recipeInstance <- components.recipeInstanceManager.update(recipeInstanceId, _.recordExecutionOutcome(outcome))
        retry = timer.sleep(delay.milliseconds) *> recipeInstance.executions(outcome.transitionExecutionId).execute
        cancelToken <- effect.runCancelable(retry)(asyncOutcomeCallback).to[F]
        _ <- scheduledRetries.update(_ + (outcome.transitionExecutionId -> cancelToken))
      } yield ()
    }

    private def cancelScheduledExecution(transitionExecutionId: Long): F[Unit] =
      scheduledRetries.get.flatMap { cancelTokenOf =>
        effect.runAsync(cancelTokenOf(transitionExecutionId)) {
          case Right(_) =>
            IO.delay(logger.info(s"Transition execution with id $transitionExecutionId cancelled"))
          case Left(e) =>
            IO.delay(logger.error("Cancellation of transition execution failed", e))
        }.to[F]
      }
  }
}
