package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.catseffect.{AsyncSupport, RefState, RefSupport, SyncSupport}
import com.ing.baker.runtime.catseffect.AsyncSupport.toAsync
import com.ing.baker.runtime.catseffect.SyncSupport.syntax._
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.model.{BakerComponents, FireSensoryEventRejection}
import com.ing.baker.runtime.scaladsl.{EventInstance, EventReceived, EventRejected, RecipeInstanceCreated}
import com.typesafe.scalalogging.LazyLogging
import fs2.Stream

import scala.jdk.OptionConverters.RichOptional
import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.jdk.DurationConverters._
import scala.concurrent.duration._

object RecipeInstance {
  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String, settings: RecipeInstanceConfig)(implicit components: BakerComponents[F], async: AsyncSupport[F], refSupport: RefSupport[F]): F[RecipeInstance[F]] =
    for {
      timestamp <- async.pure(System.currentTimeMillis())
      state <- refSupport.of[RecipeInstanceState[F]](RecipeInstanceState.empty[F](recipeInstanceId, recipe, timestamp))
      recipeInstanceCreated = RecipeInstanceCreated(timestamp, recipe.recipeId, recipe.name, recipeInstanceId)
      _ <- async.delay(components.logging.recipeInstanceCreated(recipeInstanceCreated))
      _ <- components.eventStream.publish(recipeInstanceCreated)
    } yield RecipeInstance(recipeInstanceId, settings, state)

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)
}

case class RecipeInstance[F[_]](recipeInstanceId: String, config: RecipeInstanceConfig, state: RefState[F, RecipeInstanceState[F]]) extends LazyLogging {

  private def updateStateAndNotify[A](update: RecipeInstanceState[F] => (RecipeInstanceState[F], A))(implicit async: AsyncSupport[F]): F[A] =
    for {
      resultAndListeners <- state.modify { current =>
        val (next, result) = update(current)

        // Check for idle transition
        val (idleListeners, stateAfterIdleClear) =
          if (next.isInactive && !current.isInactive) (next.idleListeners, next.copy(idleListeners = Set.empty[RecipeInstanceState.Listener[F]]))
          else (Set.empty[RecipeInstanceState.Listener[F]], next)

        // Check for newly fired events
        val newEventNames = next.events.map(_.name).toSet -- current.events.map(_.name).toSet
        val eventListeners = newEventNames.flatMap(name => stateAfterIdleClear.eventListeners.getOrElse(name, Set.empty))
        val stateAfterEventClear = stateAfterIdleClear.copy(eventListeners = stateAfterIdleClear.eventListeners -- newEventNames)

        // Combine all listeners to notify and return the final state
        val allListeners = idleListeners ++ eventListeners
        (stateAfterEventClear, (result, allListeners))
      }
      (result, listenersToNotify) = resultAndListeners
      _ <- listenersToNotify.toList.foldLeft(async.unit) { (acc, listener) =>
        acc.flatMap(_ => listener.complete)
      }
    } yield result

  def fireEventStream(input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Either[FireSensoryEventRejection, Stream[F, EventInstance]]] =
    for {
      currentTime <- async.pure(System.currentTimeMillis())
      currentState <- state.get
      validated <- currentState.validateExecution(input, correlationId, currentTime) match {
        case Left((rejection, _)) =>
          for {
            eventRejected <- async.delay(EventRejected(currentTime, recipeInstanceId, correlationId, input.name, rejection.asReason))
            _ <- async.delay(components.logging.eventRejected(eventRejected))
            _ <- components.eventStream.publish(eventRejected)
          } yield Left(rejection)
        case Right(execution) =>
          async.pure(Right(execution))
      }
      result <- validated match {
        case Left(rejection) =>
          async.pure(Left(rejection))
        case Right(initialExecution) =>
          components.eventStream.publish(EventReceived(currentTime, currentState.recipe.name, currentState.recipe.recipeId, recipeInstanceId, correlationId, input.name))
            .map(_ => Right(baseCase(initialExecution)
              .collect { case Some(output) => output.filterNot(config.ingredientsFilter.asScala.toSeq) }))
      }
    } yield result

  def stopRetryingInteraction(interactionName: String)(implicit async: AsyncSupport[F]): F[Unit] =
    for {
      transitionExecution <- getInteractionTransitionExecution(interactionName)
      _ <- updateStateAndNotify { s =>
        val nextState = s
          .removeRetryingExecution(transitionExecution.id)
          .recordFailedExecution(transitionExecution, ExceptionStrategyOutcome.BlockTransition)
        (nextState, ())
      }
    } yield ()

  def retryBlockedInteraction(interactionName: String)(implicit components: BakerComponents[F], async: AsyncSupport[F]): Stream[F, EventInstance] =
    Stream.force {
        for {
          transitionExecution <- getInteractionTransitionExecution(interactionName)
        } yield inductionStep(transitionExecution, Left(ExceptionStrategyOutcome.RetryWithDelay(0)))
      }
      .collect { case Some(output) => output }

  def resolveBlockedInteraction(interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], async: AsyncSupport[F]): Stream[F, EventInstance] =
    Stream.force {
        for {
          transitionExecution <- getInteractionTransitionExecution(interactionName)
          newOutcome <- transitionExecution.validateEventForResolvingBlockedInteraction(eventInstance)
        } yield inductionStep(transitionExecution, Right(Some(newOutcome)))
      }
      .collect { case Some(output) => output }

  /** The "base case" is the very 1st step in the stream of executing transitions that create EventInstances  */
  private def baseCase(transitionExecution: TransitionExecution)(implicit components: BakerComponents[F], async: AsyncSupport[F]): Stream[F, Option[EventInstance]] =
    for {
      _ <- Stream.eval(state.update(_.addExecution(transitionExecution)))
      outcome <- Stream.eval(transitionExecution.execute)
      output <- inductionStep(transitionExecution, outcome)
    } yield output

  /** The "induction step" is the "repeating" 2nd, 3rd... nth step in the stream of executing transitions that create
    * EventInstances, notice the recursion when there exist enabled transitions, which are outcome of executing this step
    */
  private def inductionStep(finishedExecution: TransitionExecution, outcome: TransitionExecution.Outcome)(implicit components: BakerComponents[F], async: AsyncSupport[F]): Stream[F, Option[EventInstance]] =
    for {
      outputAndEnabledExecutions <- Stream.eval(handleExecutionOutcome(finishedExecution)(outcome))
      (first, enabledExecutions) = outputAndEnabledExecutions
      next <- enabledExecutions.foldLeft(Stream.emit(first).covary[F]) { (stream, enabled) =>
        stream merge Stream.force(
          enabled.execute.map(inductionStep(enabled, _)))
      }
    } yield next

  private def handleExecutionOutcome(finishedExecution: TransitionExecution)(outcome: TransitionExecution.Outcome)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[(Option[EventInstance], Set[TransitionExecution])] =
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
          .map(_ => None -> Set.empty[TransitionExecution])

      case Left(strategy @ ExceptionStrategyOutcome.RetryWithDelay(delay)) =>
        for {
          _ <- state.update(_
            .recordFailedExecution(finishedExecution, strategy)
            .addRetryingExecution(finishedExecution.id))
          _ <- async.delay(components.logging.scheduleRetry(recipeInstanceId, finishedExecution.transition, delay))
          finalOutcome <- async.sleep(delay.milliseconds).flatMap(_ => {
            state.get.flatMap { currentState =>
              if (currentState.retryingExecutions.contains(finishedExecution.id)) {
                val currentTransitionExecution = currentState.executions(finishedExecution.id)
                val removeRetryState = updateStateAndNotify(s => (s.removeRetryingExecution(finishedExecution.id), ()))
                removeRetryState.flatMap(_ =>
                  currentTransitionExecution
                    .execute
                    .flatMap(handleExecutionOutcome(currentTransitionExecution)))
              } else
                async.pure[(Option[EventInstance], Set[TransitionExecution])](None -> Set.empty)
            }
          })
        } yield finalOutcome
    }

  private def scheduleIdleStop(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] = {
    def schedule: F[Unit] =
      state.get.flatMap { currentState =>
        config.idleTTL.toScala match {
          case Some(idleTTL) if currentState.isInactive =>
            async.sleep(idleTTL.toScala).flatMap(_ => confirmIdleStop(currentState.sequenceNumber, idleTTL.toScala))
          case _ => async.unit
        }
      }

    def confirmIdleStop(sequenceNumber: Long, originalIdleTTL: FiniteDuration): F[Unit] =
      state.get.flatMap { currentState =>
        if (currentState.isInactive && currentState.sequenceNumber == sequenceNumber)
          components.recipeInstanceManager.idleStop(recipeInstanceId)
            .flatMap(_ => async.delay(components.logging.idleStop(recipeInstanceId, originalIdleTTL)))
        else async.unit
      }

    // Start the schedule computation in the background as a fiber and discard the result
    // This allows the idle stop to happen asynchronously without blocking
    async.startAndForget(schedule)
  }

  private def getInteractionTransitionExecution(interactionName: String)(implicit effect: SyncSupport[F]): F[TransitionExecution] =
    effect.flatMap(state.get)(_.getInteractionExecution(interactionName) match {
      case None =>
        effect.raiseError(new FatalInteractionException(s"No interaction with name $interactionName within instance state with id $recipeInstanceId"))
      case Some(interactionExecution) =>
        effect.pure(interactionExecution)
    })
}