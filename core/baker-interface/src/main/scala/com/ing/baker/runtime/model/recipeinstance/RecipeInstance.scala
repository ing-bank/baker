package com.ing.baker.runtime.model.recipeinstance

import cats.data.EitherT
import cats.effect.concurrent.Ref
import cats.effect.{ConcurrentEffect, Sync, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.RecipeInstanceEventValidation.OrphanTransitionExecution
import com.ing.baker.runtime.scaladsl.{EventInstance, EventReceived, RecipeInstanceCreated}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging
import fs2.Stream

import scala.concurrent.duration._

case class RecipeInstance[F[_]](
                                 recipeInstanceId: String,
                                 recipe: CompiledRecipe,
                                 createdOn: Long,
                                 settings: RecipeInstance.Settings,
                                 state: Ref[F, RecipeInstanceState],
                                 runningSequences: Ref[F, Map[Long, ExecutionSequence[F]]],
                               ) extends LazyLogging {

  /** Validates an attempt to fire an event, and if valid, executes the cascading effect of firing the event.
    * The returning effect will resolve right after the event has been recorded, but asynchronously cascades the recipe
    * instance execution semantics.
    *
    * @return either a validation rejection or TODO.
    *         Note that the operation is wrapped within an effect because 2 reasons, first, the validation checks for
    *         current time, and second, if there is a rejection a message is logged, both are suspended into F.
    */
  def fire(currentTime: Long, input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, Stream[F, EventInstance]] = {
    for {
      currentState <- EitherT.liftF(state.get)
      orphanInitialExecution <- logRejectionReasonIfAny(currentState.validateExecution(input, correlationId, currentTime))
    } yield Stream.force(for {
      startedExecutionSequence <- ExecutionSequence.build[F](recipeInstance = this)
      initialExecution = orphanInitialExecution(startedExecutionSequence.sequenceId)
      _ <- state.update(_.addExecution(initialExecution))
      _ <- runningSequences.update(_ + (startedExecutionSequence.sequenceId -> startedExecutionSequence))
      _ <- components.eventStream.publish(EventReceived(
        currentTime, recipe.name, recipe.recipeId, recipeInstanceId, correlationId, input))
    } yield startedExecutionSequence.base(initialExecution))
  }

  def stopRetryingInteraction(interactionName: String)(implicit effect: Sync[F]): F[Unit] =
    executeOnRunningSequenceOf(interactionName)((_, execution, sequence) =>
      sequence.stopRetryingInteraction(execution))

  def retryBlockedInteraction(interactionName: String)(implicit effect: Sync[F]): F[Unit] =
    executeOnRunningSequenceOf(interactionName)((_, execution, sequence) =>
      sequence.retryBlockedInteraction(execution))

  def resolveBlockedInteraction(interactionName: String, eventInstance: EventInstance)(implicit effect: Sync[F]): F[Unit] =
    executeOnRunningSequenceOf(interactionName)((transition, execution, sequence) =>
      sequence.resolveBlockedInteraction(transition, execution, eventInstance))

  private[recipeinstance] def executeOnRunningSequenceOf(interactionName: String)(f: (InteractionTransition, TransitionExecution, ExecutionSequence[F]) => F[Unit])(implicit effect: Sync[F]): F[Unit] =
    for {
      transitionAndExecution <- getExecution(interactionName)
      (transition, execution) = transitionAndExecution
      sequence <- getSequence(execution.executionSequenceId)
      _ <- f(transition, execution, sequence)
    } yield ()

  private def getExecution(interactionName: String)(implicit effect: Sync[F]): F[(InteractionTransition, TransitionExecution)] =
    for {
      currentState <- state.get
      transitionAndExecution <- currentState.getInteractionExecution(interactionName) match {
        case None =>
          effect.raiseError(new IllegalArgumentException(s"No interaction with name $interactionName within instance state with id $recipeInstanceId"))
        case Some(transitionAndExecution) =>
          effect.pure(transitionAndExecution)
      }
    } yield transitionAndExecution

  private def getSequence(executionSequenceId: Long)(implicit effect: Sync[F]): F[ExecutionSequence[F]] =
    for {
      currentRunningSequences <- runningSequences.get
      sequence <- currentRunningSequences.get(executionSequenceId) match {
        case None =>
          effect.raiseError(new IllegalStateException(s"Transition execution has wrong owner sequence id $executionSequenceId"))
        case Some(sequence) =>
          effect.pure(sequence)
      }
    } yield sequence

  /** Helper function to log and remove the textual rejection reason of the `fire` operation. It basically exchanges the
    * String inside the returning `Either` for an external effect `F`.
    *
    * @param validation
    * @param effect
    * @return
    */
  private def logRejectionReasonIfAny(validation: Either[(FireSensoryEventRejection, String), OrphanTransitionExecution])(implicit effect: Sync[F]): EitherT[F, FireSensoryEventRejection, OrphanTransitionExecution] = {
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

object RecipeInstance {

  case class Settings(idleTTL: Option[FiniteDuration],
                      encryption: Encryption,
                      ingredientsFilter: Seq[String])

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String, settings: Settings)(implicit components: BakerComponents[F], effect: Sync[F], timer: Timer[F]): F[RecipeInstance[F]] =
    for {
      timestamp <- timer.clock.realTime(MILLISECONDS)
      state <- Ref.of[F, RecipeInstanceState](RecipeInstanceState.empty(recipeInstanceId, recipe, timestamp))
      runningSequences <- Ref.of[F, Map[Long, ExecutionSequence[F]]](Map.empty)
      _ <- components.eventStream.publish(RecipeInstanceCreated(timestamp, recipe.recipeId, recipe.name, recipeInstanceId))
    } yield RecipeInstance(recipeInstanceId, recipe, timestamp, settings, state, runningSequences)

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)
}
