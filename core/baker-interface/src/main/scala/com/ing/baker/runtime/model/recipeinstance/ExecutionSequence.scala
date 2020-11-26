package com.ing.baker.runtime.model.recipeinstance

import cats.effect.concurrent.Ref
import cats.effect.{ConcurrentEffect, IO, Timer}
import cats.implicits._
import com.ing.baker.il.petrinet.{InteractionTransition, Place}
import com.ing.baker.petrinet.api.{Marking, marshalMarking}
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.scaladsl.EventInstance
import fs2._

import scala.concurrent.duration._

object ExecutionSequence {

  def build[F[_]](recipeInstance: RecipeInstance[F])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): F[ExecutionSequence[F]] =
    for {
      retries <- Ref.of[F, Set[Long]](Set.empty)
      executionSequence = new ExecutionSequence[F](
        recipeInstance = recipeInstance,
        retryingTransitions = retries)
    } yield executionSequence
}

case class ExecutionSequence[F[_]] private[recipeinstance](sequenceId: Long = TransitionExecution.generateId,
                                                           recipeInstance: RecipeInstance[F],
                                                           retryingTransitions: Ref[F, Set[Long]]
                                                          )(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]) {

  def base(transitionExecution: TransitionExecution): Stream[F, EventInstance] =
    step(transitionExecution).collect { case Some(output) => output }

  /** Inductive step of the recipe instance execution semantics.
    * Attempts to progress the execution of the recipe instance from the outcome of a previous execution.
    *
    * This is separated because we must be careful to take only the latest state of the recipe instance by fetching it
    * from the RecipeInstanceManager component, this is because effects are happening asynchronously.
    *
    * Note that the execution effects are still suspended and should be run on due time to move the recipe instance state
    * forward with the resulting TransitionExecution.Outcome.
    *
    * @param transitionExecution
    * @return
    */
  def step(transitionExecution: TransitionExecution): Stream[F, Option[EventInstance]] = {
    Stream.eval(transitionExecution.execute >>= handleExecutionOutcome).flatMap {
      case (output, enabledTransitions) =>
        val first = Stream.emit(output).covary[F]
        enabledTransitions.foldLeft(first)(_ merge step(_))
    }
  }

  def stopRetryingInteraction(execution: TransitionExecution): F[Unit] =
    for {
      newOutcome <- execution.stopRetryingInteraction
      _ <- retryingTransitions.update(_ - execution.id)
      _ <- handleExecutionOutcome(newOutcome)
    } yield ()

  def retryBlockedInteraction(execution: TransitionExecution): F[Unit] =
    for {
      newOutcome <- execution.retryBlockedInteraction
      _ <- handleExecutionOutcome(newOutcome)
    } yield ()

  def resolveBlockedInteraction(execution: TransitionExecution, eventInstance: EventInstance): F[Unit] =
    for {
      newOutcome <- execution.resolveBlockedInteraction(eventInstance)
      _ <- handleExecutionOutcome(newOutcome)
    } yield ()

  private def handleExecutionOutcome(outcome: TransitionExecution.Outcome): F[(Option[EventInstance], Set[TransitionExecution])] =
    outcome match {

      case outcome: TransitionExecution.Outcome.Completed =>
        for {
          enabledExecutions <- recipeInstance.state.modify(_.recordCompletedExecutionOutcome(outcome))
          _ <- scheduleIdleStop
        } yield outcome.output -> enabledExecutions

      case outcome: TransitionExecution.Outcome.Failed =>

        outcome.exceptionStrategy match {
          case FailureStrategy.Continue(marking, output) =>
            handleExecutionOutcome(TransitionExecution.Outcome.Completed(
              executionSequenceId = outcome.executionSequenceId,
              transitionExecutionId = outcome.transitionExecutionId,
              transitionId = outcome.transitionId,
              correlationId = outcome.correlationId,
              timeStarted = outcome.timeStarted,
              timeCompleted = outcome.timeFailed,
              consumed = outcome.consume,
              produced = marshalMarking(marking),
              output = output))

          case FailureStrategy.BlockTransition =>
            recipeInstance.state
              .update(_.transitionExecutionToFailedState(outcome))
              .as(None -> Set.empty[TransitionExecution])

          case FailureStrategy.RetryWithDelay(delay) =>
            for {
              currentState <- recipeInstance.state.updateAndGet(_.transitionExecutionToFailedState(outcome))
              _ <- retryingTransitions.update(_ + outcome.transitionExecutionId)
              finalOutcome <- timer.sleep(delay.milliseconds) *> retryingTransitions.get.flatMap { retrying =>
                if (retrying.contains(outcome.transitionExecutionId))
                   currentState
                    .executions(outcome.transitionExecutionId)
                    .execute.flatMap(handleExecutionOutcome)
                    .flatTap(_ => retryingTransitions.update(_ - outcome.transitionExecutionId))
                else
                  effect.pure[(Option[EventInstance], Set[TransitionExecution])](None -> Set.empty)
              }
            } yield finalOutcome
        }
    }

  private def scheduleIdleStop: F[Unit] = {

    def schedule: F[Unit] =
      recipeInstance.state.get.flatMap { currentState =>
        recipeInstance.settings.idleTTL match {
          case Some(idleTTL) if currentState.isInactive =>
            timer.sleep(idleTTL) *> confirmIdleStop(currentState.sequenceNumber)
          case _ => effect.unit
        }
      }

    def confirmIdleStop(sequenceNumber: Long): F[Unit] =
      recipeInstance.state.get.flatMap { currentState =>
        if (currentState.isInactive && currentState.sequenceNumber == sequenceNumber)
          components.recipeInstanceManager.idleStop(recipeInstance.recipeInstanceId)
        else effect.unit
      }

    effect.runAsync(schedule)(_ => IO.unit).to[F]
  }
}
