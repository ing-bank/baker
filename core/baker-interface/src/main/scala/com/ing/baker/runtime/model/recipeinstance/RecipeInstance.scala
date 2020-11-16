package com.ing.baker.runtime.model.recipeinstance

import cats.Functor
import cats.data.EitherT
import cats.effect.concurrent.Ref
import cats.effect.{ConcurrentEffect, IO, Sync, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.execution.{EventsLobby, ExecutionSequence, TransitionExecution}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.duration._

case class RecipeInstance[F[_]](
                                 recipeInstanceId: String,
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
  def fire(input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, EventsLobby[F]] =
    for {
      currentTime <- ok ( timer.clock.realTime(MILLISECONDS) )
      currentState <- ok ( state.get )
      initialExecution <- logRejectionReasonIfAny(
        currentState.validateExecution(input, correlationId, currentTime))
      startedExecutionSequence <- ok ( ExecutionSequence.base[F](recipeInstance = this, initialExecution) )
      _ <- ok ( addRunningSequence(startedExecutionSequence) )
    } yield startedExecutionSequence.eventsLobby

  def stopRetryingInteraction(interactionName: String)(implicit effect: Sync[F]): F[Unit] =
    executeOnRunningSequenceOf(interactionName)((_, execution, sequence) =>
      sequence.stopRetryingInteraction(execution))

  def retryBlockedInteraction(interactionName: String)(implicit effect: Sync[F]): F[Unit] =
    executeOnRunningSequenceOf(interactionName)((_, execution, sequence) =>
      sequence.retryBlockedInteraction(execution))

  def resolveBlockedInteraction(interactionName: String, eventInstance: EventInstance)(implicit effect: Sync[F]): F[Unit] =
    executeOnRunningSequenceOf(interactionName)((transition, execution, sequence) =>
      sequence.resolveBlockedInteraction(transition, execution, eventInstance))

  private[recipeinstance] def addRunningSequence(sequence: ExecutionSequence[F]): F[Unit] =
    runningSequences.update(_ + (sequence.sequenceId -> sequence))

  private[recipeinstance] def removeRunningSequence(sequenceId: Long): F[Unit] =
    runningSequences.update(_ - sequenceId)

  private[recipeinstance] def executeOnRunningSequenceOf(interactionName: String)(f: (InteractionTransition, TransitionExecution, ExecutionSequence[F]) => F[Unit])(implicit effect: Sync[F]): F[Unit] =
    for {
      transitionAndExecution <- getExecution(interactionName)
      (transition, execution) = transitionAndExecution
      sequence <- getSequence(execution.executionSequenceId)
      _ <- f(transition, execution, sequence)
    } yield ()

  private def ok[A](fa: F[A])(implicit effect: Functor[F]): EitherT[F, FireSensoryEventRejection, A] =
    EitherT[F, FireSensoryEventRejection, A](fa.map(Right(_)))

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

  private[recipeinstance] def logImpossibleException(cause: Throwable): IO[Unit] = {
    val message = """Imminent bug, unexpected exception when firing an event, it should be impossible to have exceptions at this point.
                    |The execution.execute should wrap any exception from interaction instances and report them as failed outcomes.
                    |The process of firing an event is free of exceptions besides the previously mentioned, this is used to properly
                    |implement the cats effect ConcurrentEffect.runAsync method.
                    |""".stripMargin
    IO.delay(logger.error(message, new IllegalStateException(message, cause)))
  }
}

object RecipeInstance {

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String)(implicit effect: Sync[F], timer: Timer[F]): F[RecipeInstance[F]] =
    for {
      timestamp <- timer.clock.realTime(MILLISECONDS)
      state <- Ref.of[F, RecipeInstanceState](RecipeInstanceState.empty(recipeInstanceId, recipe, timestamp))
      runningSequences <- Ref.of[F, Map[Long, ExecutionSequence[F]]](Map.empty)
    } yield RecipeInstance(recipeInstanceId, state, runningSequences)

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)
}
