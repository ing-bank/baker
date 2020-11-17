package com.ing.baker.runtime.model.recipeinstance.execution

import cats.implicits._
import cats.effect.concurrent.Ref
import cats.effect.{CancelToken, ConcurrentEffect, IO, Timer}
import com.ing.baker.il.petrinet.{InteractionTransition, Place}
import com.ing.baker.petrinet.api.{Marking, marshalMarking}
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.recipeinstance.execution.ExecutionSequence.ScheduledRetries
import com.ing.baker.runtime.model.recipeinstance.{FailureStrategy, RecipeInstance, RecipeInstanceState}
import com.ing.baker.runtime.scaladsl.EventInstance

import scala.concurrent.duration._

object ExecutionSequence {

  /** Base case of the recipe instance execution semantics.
    *
    * @param recipeInstance.recipeInstanceId
    * @param transitionExecution
    * @param logger
    * @param components
    * @param effect
    * @param timer
    * @tparam F
    * @return
    */
  def base[F[_]](recipeInstance: RecipeInstance[F], initialExecution: TransitionExecution)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): F[ExecutionSequence[F]] =
    for {
      eventsLobby <- EventsLobby.build[F]
      scheduledRetries <- Ref.of[F, Map[Long, CancelToken[F]]](Map.empty)
      executionSequence = new ExecutionSequence[F](
        recipeInstance = recipeInstance,
        scheduledRetries = scheduledRetries,
        eventsLobby = eventsLobby)
      _ <- recipeInstance.runningSequences.update(_ + (executionSequence.sequenceId -> executionSequence))
      _ <- recipeInstance.state.update(_.addExecution(initialExecution.setOwner(executionSequence.sequenceId)))
      _ <- executionSequence.step(initialExecution)
    } yield executionSequence

  type ScheduledRetries[F[_]] = Ref[F, Map[Long, CancelToken[F]]]
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
                                                           scheduledRetries: ScheduledRetries[F],
                                                           eventsLobby: EventsLobby[F]
                                                          )(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]) {

  def step(transitionExecution: TransitionExecution): F[Unit] =
    effect.runAsync(transitionExecution.execute)(asyncOutcomeCallback).to[F]

  private def asyncOutcomeCallback(asyncOutcome: Either[Throwable, TransitionExecution.Outcome]): IO[Unit] =
    effect.toIO(asyncOutcome match {
      case Right(outcome: TransitionExecution.Outcome.Completed) =>
        handleCompletedOutcome(outcome)
      case Right(outcome: TransitionExecution.Outcome.Failed) =>
        handleFailureOutcome(outcome)
      case Left(e) =>
        recipeInstance.logImpossibleException(e).to[F]
    })

  private def handleCompletedOutcome(outcome: TransitionExecution.Outcome.Completed): F[Unit] =
    for {
      enabledExecutions <- recipeInstance.state.modify(_.recordCompletedExecutionOutcome(outcome))
      _ <- eventsLobby.reportTransitionFinished(outcome, enabledExecutions, outcome.output)
      _ <- enabledExecutions.toList.traverse(step)
      _ <- scheduleIdleStop
    } yield ()

  private def handleFailureOutcome(outcome: TransitionExecution.Outcome.Failed): F[Unit] =
    outcome.exceptionStrategy match {
      case FailureStrategy.Continue(marking, output) =>
        handleCompletedOutcome(TransitionExecution.Outcome.Completed(
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
          // TODO CLEAN
          _ = (Console.RED_B +
            s""" Transition failed: ${outcome.failureReason}
              |""".stripMargin + Console.RESET)
          _ <- eventsLobby.reportTransitionFinished(outcome)
        } yield ()

      case FailureStrategy.RetryWithDelay(delay) =>
        for {
          currentState <- recipeInstance.state.updateAndGet(_.transitionExecutionToFailedState(outcome))
          retry = timer.sleep(delay.milliseconds) *> currentState.executions(outcome.transitionExecutionId).execute
          cancelToken <- effect.runCancelable(retry)(asyncOutcomeCallback).to[F]
          _ <- scheduledRetries.update(_ + (outcome.transitionExecutionId -> cancelToken))
        } yield ()
    }

  def cancelScheduledExecution(transitionExecutionId: Long): F[Unit] =
    for {
      cancelTokenOf <- scheduledRetries.get
      cancelToken <- cancelTokenOf.get(transitionExecutionId) match {
        case Some(token) =>
          effect.pure(token)
        case None =>
          effect.raiseError[CancelToken[F]](new IllegalArgumentException("No transition execution with id $transitionExecutionId in this execution sequence"))
      }
      _ <- effect.runAsync(cancelToken) {
        case Right(_) =>
          // TODO
          //IO.delay(recipeInstance.logger.info(s"Transition execution with id $transitionExecutionId cancelled"))
          IO.unit
        case Left(e) =>
          // TODO
          //IO.delay(recipeInstance.logger.error("Cancellation of transition execution failed", e))
          IO.unit
      }.to[F]
    } yield ()

  def scheduleIdleStop: F[Unit] =
    for {
      currentState <- recipeInstance.state.get
      _ <- recipeInstance.settings.idleTTL match {
        case Some(idleTTL) if currentState.isInactive =>
          timer.sleep(idleTTL) *> confirmIdleStop(currentState.sequenceNumber)
        case _ =>
          effect.unit
      }
    } yield ()

  def confirmIdleStop(sequenceNumber: Long): F[Unit] =
    for {
      currentState <- recipeInstance.state.get
      _ <-
        if (currentState.isInactive && currentState.sequenceNumber == sequenceNumber)
          components.recipeInstanceManager.idleStop(recipeInstance.recipeInstanceId)
        else
          effect.unit
    } yield ()

  // TODO all of these must be found by the recipe instance manager for execution, for such we must save these contexts into the manager besides the recipe instance
  def stopRetryingInteraction(execution: TransitionExecution): F[Unit] =
    if (execution.isRetrying)
      for {
        _ <- cancelScheduledExecution(execution.id)
        // TODO all of this can be done inside the execution and should be refactored together with it
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- execution.getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          execution.id, execution.transition.id, execution.correlationId, timestamp, timestamp, marshalMarking(execution.consume), execution.input, failureReason, FailureStrategy.BlockTransition)
        // TODO ^
        _ <- handleFailureOutcome(outcome)
      } yield ()
    else effect.raiseError(new IllegalArgumentException("Interaction is not retrying"))

  def retryBlockedInteraction(execution: TransitionExecution): F[Unit] =
    if (execution.isBlocked)
      for {
        // TODO all of this can be done inside the execution and should be refactored together with it
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- execution.getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          execution.id, execution.transition.id, execution.correlationId, timestamp, timestamp, marshalMarking(execution.consume), execution.input, failureReason, FailureStrategy.RetryWithDelay(0))
        // TODO ^
        _ <- handleFailureOutcome(outcome)
      } yield ()
    else effect.raiseError(new IllegalArgumentException("Interaction is not blocked"))

  def resolveBlockedInteraction(interaction: InteractionTransition, execution: TransitionExecution, eventInstance: EventInstance): F[Unit] =
    if (execution.isBlocked)
      for {
        _ <- execution.validateInteractionOutput[F](interaction, Some(eventInstance))
        // TODO this is awaiting the Transition Execution refactor
        petriNet = execution.recipe.petriNet
        producedMarking: Marking[Place] = execution.createOutputMarkingForPetriNet(petriNet.outMarking(interaction), Some(eventInstance))
        transformedEvent: Option[EventInstance] = execution.transformOutputWithTheInteractionTransitionOutputTransformers(interaction, Some(eventInstance))
        // TODO all of this can be done inside the execution and should be refactored together with it
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- execution.getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          execution.id, execution.transition.id, execution.correlationId, timestamp, timestamp, marshalMarking(execution.consume), execution.input, failureReason, FailureStrategy.Continue(producedMarking, transformedEvent))
        // TODO ^
        _ <- handleFailureOutcome(outcome)
      } yield ()
    else
      effect.raiseError(new IllegalArgumentException("Interaction is not blocked"))
}
