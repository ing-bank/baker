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

/** TODO rewrite this within the context of 1 event
  * Inductive step of the recipe instance execution semantics.
  * Attempts to progress the execution of the recipe instance from the outcome of a previous execution.
  *
  * This is separated because we must be careful to take only the latest state of the recipe instance by fetching it
  * from the RecipeInstanceManager component, this is because effects are happening asynchronously.
  *
  * Note that the execution effects are still suspended and should be run on due time to move the recipe instance state
  * forward with the resulting TransitionExecution.Outcome.
  *
  * @param components
  * @param effect
  * @param timer
  * @tparam F
  * @return
  */
case class ExecutionSequence[F[_]] private[recipeinstance](sequenceId: Long = TransitionExecution.generateId,
                                                           recipeInstance: RecipeInstance[F],
                                                           retryingTransitions: Ref[F, Set[Long]]
                                                          )(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]) {

  def base(transitionExecution: TransitionExecution): Stream[F, EventInstance] =
    step(transitionExecution).collect { case Some(output) => output }

  def step(transitionExecution: TransitionExecution): Stream[F, Option[EventInstance]] = {
    Stream.eval(transitionExecution.execute.flatMap(handleExecutionOutcome)).flatMap {
      case (output, enabledTransitions) =>

        /*
        println(Console.MAGENTA + "\n" +
          s"""Finished: transition = ${transitionExecution.transition.label} | executionId = ${transitionExecution.id}
          |Output: ${output.map(_.name)}
          |Enabled: ${enabledTransitions.map(t => "\n\t" + t.transition.label + " | transitionId = " + t.transition.id + " | executionId = " + t.id)}
          |""".stripMargin + Console.RESET)
         */

        val first = Stream.emit(output).covary[F]
        enabledTransitions.foldLeft(first)(_ merge step(_))
    }
  }

  private def handleExecutionOutcome(outcome: TransitionExecution.Outcome): F[(Option[EventInstance], Set[TransitionExecution])] =
    outcome match {
      case outcome: TransitionExecution.Outcome.Completed =>
        for {
          enabledExecutions <- recipeInstance.state.modify(_.recordCompletedExecutionOutcome(outcome))
          _ <- scheduleIdleStop
        } yield outcome.output -> enabledExecutions

      case outcome: TransitionExecution.Outcome.Failed =>

        /*
        println(Console.RED_B +
          s""" Failed: transitionId = ${outcome.transitionId}
          | executionId = ${outcome.transitionExecutionId}
          | Strategy: ${outcome.exceptionStrategy}
          | Reason: ${outcome.failureReason}
          |""".stripMargin + Console.RESET)
         */

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
            for {
              _ <- recipeInstance.state.update(_.transitionExecutionToFailedState(outcome))
              //_ <- eventsLobby.reportTransitionFinished(outcome)
            } yield None -> Set.empty[TransitionExecution]

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

  def scheduleIdleStop: F[Unit] = {
    effect.runAsync {
      recipeInstance.state.get.flatMap { currentState =>
        recipeInstance.settings.idleTTL match {
          case Some(idleTTL) if currentState.isInactive =>
            timer.sleep(idleTTL) *> confirmIdleStop(currentState.sequenceNumber)
          case _ => effect.unit
        }
      }
    }(_ => IO.unit).to[F]
  }

  def confirmIdleStop(sequenceNumber: Long): F[Unit] =
    recipeInstance.state.get.flatMap { currentState =>
      if (currentState.isInactive && currentState.sequenceNumber == sequenceNumber)
        components.recipeInstanceManager.idleStop(recipeInstance.recipeInstanceId)
      else effect.unit
    }

  // TODO all of these must be found by the recipe instance manager for execution, for such we must save these contexts into the manager besides the recipe instance
  def stopRetryingInteraction(execution: TransitionExecution): F[Unit] =
    if (execution.isRetrying)
      for {
        _ <- retryingTransitions.update(_ - execution.id)
        // TODO all of this can be done inside the execution and should be refactored together with it
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- execution.getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          executionSequenceId = execution.executionSequenceId,
          transitionExecutionId = execution.id,
          transitionId = execution.transition.id,
          execution.correlationId,
          timestamp,
          timestamp,
          marshalMarking(execution.consume),
          execution.input,
          failureReason,
          FailureStrategy.BlockTransition)
        // TODO ^
        _ <- handleExecutionOutcome(outcome)
      } yield ()
    else effect.raiseError(new IllegalArgumentException("Interaction is not retrying"))

  def retryBlockedInteraction(execution: TransitionExecution): F[Unit] =
    if (execution.isBlocked)
      for {
        // TODO all of this can be done inside the execution and should be refactored together with it
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- execution.getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          executionSequenceId = execution.executionSequenceId,
          transitionExecutionId = execution.id,
          transitionId = execution.transition.id,
          execution.correlationId,
          timestamp,
          timestamp,
          marshalMarking(execution.consume),
          execution.input,
          failureReason,
          FailureStrategy.RetryWithDelay(0))
        // TODO ^
        _ <- handleExecutionOutcome(outcome)
      } yield ()
    else effect.raiseError(new IllegalArgumentException("Interaction is not blocked"))

  def resolveBlockedInteraction(interaction: InteractionTransition, execution: TransitionExecution, eventInstance: EventInstance): F[Unit] =
    if (execution.isBlocked)
      for {
        _ <- execution.validateInteractionOutput[F](interaction, Some(eventInstance))
        // TODO this is awaiting the Transition Execution refactor
        petriNet = execution.recipe.petriNet
        producedMarking: Marking[Place] = execution.createOutputMarking(petriNet.outMarking(interaction), Some(eventInstance))
        transformedEvent: Option[EventInstance] = execution.transformOutputWithTheInteractionTransitionOutputTransformers(interaction, Some(eventInstance))
        // TODO all of this can be done inside the execution and should be refactored together with it
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- execution.getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          executionSequenceId = execution.executionSequenceId,
          transitionExecutionId = execution.id,
          transitionId = execution.transition.id,
          execution.correlationId,
          timestamp,
          timestamp,
          marshalMarking(execution.consume),
          execution.input,
          failureReason,
          FailureStrategy.Continue(producedMarking, transformedEvent)
        )
        // TODO ^
        _ <- handleExecutionOutcome(outcome)
      } yield ()
    else
      effect.raiseError(new IllegalArgumentException("Interaction is not blocked"))
}
