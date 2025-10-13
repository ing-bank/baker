package com.ing.baker.runtime.model.recipeinstance

import cats.data.EitherT
import cats.effect.kernel.Ref
import cats.effect.std.Dispatcher
import cats.effect.{Async, Deferred, IO, Sync}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.model.{BakerComponents, FireSensoryEventRejection}
import com.ing.baker.runtime.scaladsl.{EventInstance, EventReceived, EventRejected, RecipeInstanceCreated}
import com.typesafe.scalalogging.LazyLogging
import fs2.Stream

import scala.concurrent.duration._

object RecipeInstance {

  case class Config(idleTTL: Option[FiniteDuration] = Some(5.seconds),
                    ingredientsFilter: Seq[String] = Seq.empty)

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String, settings: Config)(implicit components: BakerComponents[F], async: Async[F]): F[RecipeInstance[F]] =
    for {
      timestamp <- async.pure(System.currentTimeMillis())
      state <- Ref.of[F, RecipeInstanceState[F]](RecipeInstanceState.empty(recipeInstanceId, recipe, timestamp))
      recipeInstanceCreated = RecipeInstanceCreated(timestamp, recipe.recipeId, recipe.name, recipeInstanceId)
      _ <- async.delay(components.logging.recipeInstanceCreated(recipeInstanceCreated))
      _ <- components.eventStream.publish(recipeInstanceCreated)
    } yield RecipeInstance(recipeInstanceId, settings, state)

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)
}

case class RecipeInstance[F[_]](recipeInstanceId: String, config: RecipeInstance.Config, state: Ref[F, RecipeInstanceState[F]]) extends LazyLogging {

  private def updateStateAndNotify[A](update: RecipeInstanceState[F] => (RecipeInstanceState[F], A))(implicit async: Async[F]): F[A] =
    for {
      resultAndListeners <- state.modify { current =>
        val (next, result) = update(current)

        // Check for idle transition
        val (idleListeners, stateAfterIdleClear) =
          if (next.isInactive && !current.isInactive) (next.idleListeners, next.copy(idleListeners = Set.empty[Deferred[F, Unit]]))
          else (Set.empty[Deferred[F, Unit]], next)

        // Check for newly fired events
        val newEventNames = next.events.map(_.name).toSet -- current.events.map(_.name).toSet
        val eventListeners = newEventNames.flatMap(name => stateAfterIdleClear.eventListeners.getOrElse(name, Set.empty))
        val stateAfterEventClear = stateAfterIdleClear.copy(eventListeners = stateAfterIdleClear.eventListeners -- newEventNames)

        // Combine all listeners to notify and return the final state
        val allListeners = idleListeners ++ eventListeners
        (stateAfterEventClear, (result, allListeners))
      }
      (result, listenersToNotify) = resultAndListeners
      _ <- listenersToNotify.toList.traverse_(_.complete(()))
    } yield result

  def fireEventStream(input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: Async[F]): EitherT[F, FireSensoryEventRejection, Stream[F, EventInstance]] =
    for {
      currentTime <- EitherT.liftF(async.pure(System.currentTimeMillis()))
      currentState <- EitherT.liftF(state.get)
      initialExecution <- EitherT.fromEither[F](currentState.validateExecution(input, correlationId, currentTime))
        .leftSemiflatMap { case (rejection, reason)  =>
          for {
            eventRejected <- async.delay(EventRejected(currentTime, recipeInstanceId, correlationId, input.name, rejection.asReason))
            _ <- async.delay(components.logging.eventRejected(eventRejected))
            _ <- components.eventStream.publish(eventRejected)
          } yield rejection
        }
      _ <- EitherT.liftF(components.eventStream.publish(EventReceived(currentTime, currentState.recipe.name, currentState.recipe.recipeId, recipeInstanceId, correlationId, input.name)))
    } yield baseCase(initialExecution)
      .collect { case Some(output) => output.filterNot(config.ingredientsFilter) }

  def stopRetryingInteraction(interactionName: String)(implicit components: BakerComponents[F], async: Async[F]): F[Unit] =
    for {
      transitionExecution <- getInteractionTransitionExecution(interactionName)
      _ <- updateStateAndNotify { s =>
        val nextState = s
          .removeRetryingExecution(transitionExecution.id)
          .recordFailedExecution(transitionExecution, ExceptionStrategyOutcome.BlockTransition)
        (nextState, ())
      }
    } yield ()

  def retryBlockedInteraction(interactionName: String)(implicit components: BakerComponents[F], async: Async[F]): Stream[F, EventInstance] =
    Stream.force {
        for {
          transitionExecution <- getInteractionTransitionExecution(interactionName)
        } yield inductionStep(transitionExecution, Left(ExceptionStrategyOutcome.RetryWithDelay(0)))
      }
      .collect { case Some(output) => output }

  def resolveBlockedInteraction(interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], async: Async[F]): Stream[F, EventInstance] =
    Stream.force {
        for {
          transitionExecution <- getInteractionTransitionExecution(interactionName)
          newOutcome <- transitionExecution.validateEventForResolvingBlockedInteraction(eventInstance)
        } yield inductionStep(transitionExecution, Right(Some(newOutcome)))
      }
      .collect { case Some(output) => output }

  /** The "base case" is the very 1st step in the stream of executing transitions that create EventInstances  */
  private def baseCase(transitionExecution: TransitionExecution)(implicit components: BakerComponents[F], async: Async[F]): Stream[F, Option[EventInstance]] =
    for {
      _ <- Stream.eval(state.update(_.addExecution(transitionExecution)))
      outcome <- Stream.eval(transitionExecution.execute)
      output <- inductionStep(transitionExecution, outcome)
    } yield output

  /** The "induction step" is the "repeating" 2nd, 3rd... nth step in the stream of executing transitions that create
    * EventInstances, notice the recursion when there exist enabled transitions, which are outcome of executing this step
    */
  private def inductionStep(finishedExecution: TransitionExecution, outcome: TransitionExecution.Outcome)(implicit components: BakerComponents[F], async: Async[F]): Stream[F, Option[EventInstance]] =
    for {
      outputAndEnabledExecutions <- Stream.eval(handleExecutionOutcome(finishedExecution)(outcome))
      (first, enabledExecutions) = outputAndEnabledExecutions
      next <- enabledExecutions.foldLeft(Stream.emit(first).covary[F]) { (stream, enabled) =>
        stream merge Stream.force(
          enabled.execute.map(inductionStep(enabled, _)))
      }
    } yield next

  private def handleExecutionOutcome(finishedExecution: TransitionExecution)(outcome: TransitionExecution.Outcome)(implicit components: BakerComponents[F], async: Async[F]): F[(Option[EventInstance], Set[TransitionExecution])] =
    outcome match {

      case Right(output) =>
        for {
          enabledExecutions <- updateStateAndNotify(_.recordCompletedExecution(finishedExecution, output))
          _ <- scheduleIdleStop
        } yield output -> enabledExecutions

      case Left(ExceptionStrategyOutcome.Continue(eventName)) =>
        val output: EventInstance = EventInstance(eventName, Map.empty)
        for {
          enabledExecutions <- updateStateAndNotify(_.recordFailedWithOutputExecution(finishedExecution, output))
          _ <- scheduleIdleStop
        } yield Some(output) -> enabledExecutions

      case Left(ExceptionStrategyOutcome.ContinueAsFunctionalEvent(eventName)) =>
        val output: EventInstance = EventInstance(eventName, Map.empty)
        for {
          enabledExecutions <- updateStateAndNotify(_.recordFailedWithOutputExecutionAsFunctionalEvent(finishedExecution, output))
          _ <- scheduleIdleStop
        } yield Some(output) -> enabledExecutions

      case Left(strategy @ ExceptionStrategyOutcome.BlockTransition) =>
        updateStateAndNotify(s => (s.recordFailedExecution(finishedExecution, strategy), ()))
          .as(None -> Set.empty[TransitionExecution])

      case Left(strategy @ ExceptionStrategyOutcome.RetryWithDelay(delay)) =>
        for {
          _ <- state.update(_
            .recordFailedExecution(finishedExecution, strategy)
            .addRetryingExecution(finishedExecution.id))
          _ <- async.delay(components.logging.scheduleRetry(recipeInstanceId, finishedExecution.transition, delay))
          finalOutcome <- async.sleep(delay.milliseconds) *> {
            state.get.flatMap { currentState =>
              if (currentState.retryingExecutions.contains(finishedExecution.id)) {
                val currentTransitionExecution = currentState.executions(finishedExecution.id)
                val removeRetryState = updateStateAndNotify(s => (s.removeRetryingExecution(finishedExecution.id), ()))
                removeRetryState *>
                  currentTransitionExecution
                    .execute
                    .flatMap(handleExecutionOutcome(currentTransitionExecution))
              } else
                async.pure[(Option[EventInstance], Set[TransitionExecution])](None -> Set.empty)
            }
          }
        } yield finalOutcome
    }

  private def scheduleIdleStop(implicit components: BakerComponents[F], async: Async[F]): F[Unit] = {
    def schedule: F[Unit] =
      state.get.flatMap { currentState =>
        config.idleTTL match {
          case Some(idleTTL) if currentState.isInactive =>
            async.sleep(idleTTL) *> confirmIdleStop(currentState.sequenceNumber, idleTTL)
          case _ => async.unit
        }
      }

    def confirmIdleStop(sequenceNumber: Long, originalIdleTTL: FiniteDuration): F[Unit] =
      state.get.flatMap { currentState =>
        if (currentState.isInactive && currentState.sequenceNumber == sequenceNumber)
          components.recipeInstanceManager.idleStop(recipeInstanceId) *>
            async.delay(components.logging.idleStop(recipeInstanceId, originalIdleTTL))
        else async.unit
      }
    val scheduled: IO[Unit] = Dispatcher.parallel[IO](await = true).map { dispatcher: Dispatcher[IO] =>
      dispatcher.unsafeRunAndForget(IO.delay(schedule))
    }.use(_ => IO.unit)
    Async[F].delay(scheduled)
  }

  private def getInteractionTransitionExecution(interactionName: String)(implicit effect: Sync[F]): F[TransitionExecution] =
    state.get.flatMap(_.getInteractionExecution(interactionName) match {
      case None =>
        effect.raiseError(new FatalInteractionException(s"No interaction with name $interactionName within instance state with id $recipeInstanceId"))
      case Some(interactionExecution) =>
        effect.pure(interactionExecution)
    })
}