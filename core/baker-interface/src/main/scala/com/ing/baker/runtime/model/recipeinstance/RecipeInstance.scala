package com.ing.baker.runtime.model.recipeinstance

import cats.implicits._
import cats.data.EitherT
import cats.effect.concurrent.Ref
import cats.effect.{ConcurrentEffect, Effect, IO, Sync, Timer}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl.{EventInstance, EventReceived, RecipeInstanceCreated}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging
import fs2.Stream

import scala.concurrent.duration._

object RecipeInstance {

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String, settings: Settings)(implicit components: BakerComponents[F], effect: Sync[F], timer: Timer[F]): F[RecipeInstance[F]] =
    for {
      timestamp <- timer.clock.realTime(MILLISECONDS)
      state <- Ref.of[F, RecipeInstanceState](RecipeInstanceState.empty(recipeInstanceId, recipe, timestamp))
      _ <- components.eventStream.publish(RecipeInstanceCreated(timestamp, recipe.recipeId, recipe.name, recipeInstanceId))
    } yield RecipeInstance(recipeInstanceId, settings, state)

  case class Settings(idleTTL: Option[FiniteDuration], encryption: Encryption, ingredientsFilter: Seq[String])

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)
}

case class RecipeInstance[F[_]](recipeInstanceId: String, settings: RecipeInstance.Settings, state: Ref[F, RecipeInstanceState]) extends LazyLogging {

  /** Validates an attempt to fire an event, and if valid, executes the cascading effect of firing the event.
    * The returning effect will resolve right after the event has been recorded, but asynchronously cascades the recipe
    * instance execution semantics.
    *
    * @return either a validation rejection or TODO.
    *         Note that the operation is wrapped within an effect because 2 reasons, first, the validation checks for
    *         current time, and second, if there is a rejection a message is logged, both are suspended into F.
    */
  def fire(currentTime: Long, input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, Stream[F, EventInstance]] =
    for {
      currentState <- EitherT.liftF(state.get)
      initialExecution <- logRejectionReasonIfAny(currentState.validateExecution(input, correlationId, currentTime))
      _ <- EitherT.liftF(components.eventStream.publish(EventReceived(
        currentTime, currentState.recipe.name, currentState.recipe.recipeId, recipeInstanceId, correlationId, input)))
    } yield baseCase(initialExecution)
      .collect { case Some(output) => output }

  def stopRetryingInteraction(interactionName: String)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): F[Unit] =
    for {
      transitionExecution <- getInteractionTransitionExecution(interactionName)
      _ <- state.update(_
        .removeRetryingExecution(transitionExecution.id)
        .recordFailedExecution(transitionExecution, ExceptionStrategyOutcome.BlockTransition))
    } yield ()

  def retryBlockedInteraction(interactionName: String)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): Stream[F, EventInstance] =
    Stream.force {
      for {
        transitionExecution <- getInteractionTransitionExecution(interactionName)
      } yield inductionStep(transitionExecution, Left(ExceptionStrategyOutcome.RetryWithDelay(0)))
    }
      .collect { case Some(output) => output }

  def resolveBlockedInteraction(interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): Stream[F, EventInstance] =
    Stream.force {
      for {
        transitionExecution <- getInteractionTransitionExecution(interactionName)
        newOutcome <- transitionExecution.validateEventForResolvingBlockedInteraction(eventInstance)
      } yield inductionStep(transitionExecution, Right(Some(newOutcome)))
    }
      .collect { case Some(output) => output }

  private def baseCase(transitionExecution: TransitionExecution)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): Stream[F, Option[EventInstance]] =
    for {
      _ <- Stream.eval(state.update(_.addExecution(transitionExecution)))
      outcome <- Stream.eval(transitionExecution.execute)
      output <- inductionStep(transitionExecution, outcome)
    } yield output

  /** Induction step of the recipe instance execution semantics.
    * Attempts to progress the execution of the recipe instance from the outcome of a previous execution.
    *
    * This is separated because we must be careful to take only the latest state of the recipe instance by fetching it
    * from the RecipeInstanceManager component, this is because effects are happening asynchronously.
    *
    * Note that the execution effects are still suspended and should be run on due time to move the recipe instance state
    * forward with the resulting TransitionExecution.Outcome.
    *
    * @param finishedExecution
    * @return
    */
  private def inductionStep(finishedExecution: TransitionExecution, outcome: TransitionExecution.Outcome)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): Stream[F, Option[EventInstance]] =
    for {
      outputAndEnabledExecutions <- Stream.eval(handleExecutionOutcome(finishedExecution)(outcome))
      (first, enabledExecutions) = outputAndEnabledExecutions
      next <- enabledExecutions.foldLeft(Stream.emit(first).covary[F]) { (stream, enabled) =>
        stream merge Stream.force(
          enabled.execute.map(inductionStep(enabled, _)))
      }
    } yield next

  private def handleExecutionOutcome(finishedExecution: TransitionExecution)(outcome: TransitionExecution.Outcome)(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): F[(Option[EventInstance], Set[TransitionExecution])] =
    outcome match {

      case Right(output) =>
        for {
          enabledExecutions <- state.modify(_.recordCompletedExecution(finishedExecution, output))
          _ <- scheduleIdleStop
        } yield output -> enabledExecutions

      case Left(ExceptionStrategyOutcome.Continue(eventName)) =>
        handleExecutionOutcome(finishedExecution)(Right(Some(EventInstance(eventName, Map.empty))))

      case Left(strategy @ ExceptionStrategyOutcome.BlockTransition) =>
        state
          .update(_.recordFailedExecution(finishedExecution, strategy))
          .as(None -> Set.empty[TransitionExecution])

      case Left(strategy @ ExceptionStrategyOutcome.RetryWithDelay(delay)) =>
        for {
          _ <- state.update(_
            .recordFailedExecution(finishedExecution, strategy)
            .addRetryingExecution(finishedExecution.id))
          finalOutcome <- timer.sleep(delay.milliseconds) *> state.get.flatMap { currentState =>
            if (currentState.retryingExecutions.contains(finishedExecution.id)) {
              val currentTransitionExecution = currentState.executions(finishedExecution.id)
              currentTransitionExecution
                .execute
                .flatMap(handleExecutionOutcome(currentTransitionExecution))
                .flatTap(_ => state.update(_.removeRetryingExecution(finishedExecution.id)))
            } else
              effect.pure[(Option[EventInstance], Set[TransitionExecution])](None -> Set.empty)
          }
        } yield finalOutcome
    }

  private def scheduleIdleStop(implicit components: BakerComponents[F], effect: Effect[F], timer: Timer[F]): F[Unit] = {

    def schedule: F[Unit] =
      state.get.flatMap { currentState =>
        settings.idleTTL match {
          case Some(idleTTL) if currentState.isInactive =>
            timer.sleep(idleTTL) *> confirmIdleStop(currentState.sequenceNumber)
          case _ => effect.unit
        }
      }

    def confirmIdleStop(sequenceNumber: Long): F[Unit] =
      state.get.flatMap { currentState =>
        if (currentState.isInactive && currentState.sequenceNumber == sequenceNumber)
          components.recipeInstanceManager.idleStop(recipeInstanceId)
        else effect.unit
      }

    effect.runAsync(schedule)(_ => IO.unit).to[F]
  }

  private def getInteractionTransitionExecution(interactionName: String)(implicit effect: Sync[F]): F[TransitionExecution] =
    state.get.flatMap(_.getInteractionExecution(interactionName) match {
      case None =>
        effect.raiseError(new FatalInteractionException(s"No interaction with name $interactionName within instance state with id $recipeInstanceId"))
      case Some(interactionExecution) =>
        effect.pure(interactionExecution)
    })

  /** Helper function to log and remove the textual rejection reason of the `fire` operation. It basically exchanges the
    * String inside the returning `Either` for an external effect `F`.
    *
    * @param validation
    * @param effect
    * @return
    */
  private def logRejectionReasonIfAny(validation: Either[(FireSensoryEventRejection, String), TransitionExecution])(implicit effect: Sync[F]): EitherT[F, FireSensoryEventRejection, TransitionExecution] = {
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
