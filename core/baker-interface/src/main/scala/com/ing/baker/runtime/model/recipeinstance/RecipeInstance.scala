package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.catseffect.{AsyncSupport, RefState, RefSupport, SyncSupport}
import com.ing.baker.runtime.catseffect.SyncSupport.syntax._
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.model.{BakerComponents, FireSensoryEventRejection}
import com.ing.baker.runtime.scaladsl.{EventInstance, EventReceived, EventRejected, RecipeInstanceCreated}
import com.typesafe.scalalogging.LazyLogging

import scala.jdk.OptionConverters.RichOptional
import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.jdk.DurationConverters._
import scala.concurrent.duration._
import scala.collection.mutable.ListBuffer
import java.util.concurrent.CompletableFuture
import java.util.concurrent.atomic.AtomicInteger

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

  def fireEventStream(input: EventInstance, correlationId: Option[String])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Either[FireSensoryEventRejection, Vector[EventInstance]]] =
    async.delay(ListBuffer.empty[EventInstance]).flatMap { events =>
      fireEventAndProcess(input, correlationId)(event => async.delay(events += event).map(_ => ()))
        .map(_.map(_ => events.toVector))
    }

  def fireEventAndProcess(input: EventInstance, correlationId: Option[String])(onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Either[FireSensoryEventRejection, Unit]] =
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
          val filteredOnEvent: EventInstance => F[Unit] =
            event => onEvent(event.filterNot(config.ingredientsFilter.asScala.toSeq))
          components.eventStream
            .publish(EventReceived(currentTime, currentState.recipe.name, currentState.recipe.recipeId, recipeInstanceId, correlationId, input.name))
            .flatMap(_ => baseCaseAndProcess(initialExecution, filteredOnEvent).map(_ => Right(())))
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

  def retryBlockedInteraction(interactionName: String)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Vector[EventInstance]] =
    async.delay(ListBuffer.empty[EventInstance]).flatMap { events =>
      retryBlockedInteractionAndProcess(interactionName)(event => async.delay(events += event).map(_ => ()))
        .map(_ => events.toVector)
    }

  def retryBlockedInteractionAndProcess(interactionName: String)(onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    for {
      transitionExecution <- getInteractionTransitionExecution(interactionName)
      _ <- inductionStepAndProcess(transitionExecution, Left(ExceptionStrategyOutcome.RetryWithDelay(0)), onEvent)
    } yield ()

  def resolveBlockedInteraction(interactionName: String, eventInstance: EventInstance)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Vector[EventInstance]] =
    async.delay(ListBuffer.empty[EventInstance]).flatMap { events =>
      resolveBlockedInteractionAndProcess(interactionName, eventInstance)(event => async.delay(events += event).map(_ => ()))
        .map(_ => events.toVector)
    }

  def resolveBlockedInteractionAndProcess(interactionName: String, eventInstance: EventInstance)(onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    for {
      transitionExecution <- getInteractionTransitionExecution(interactionName)
      newOutcome <- transitionExecution.validateEventForResolvingBlockedInteraction(eventInstance)
      _ <- inductionStepAndProcess(transitionExecution, Right(Some(newOutcome)), onEvent)
    } yield ()

  /** The "base case" is the very 1st step in transition execution that may create EventInstances. */
  private def baseCaseAndProcess(transitionExecution: TransitionExecution, onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    for {
      _ <- state.update(_.addExecution(transitionExecution))
      outcome <- transitionExecution.execute
      _ <- inductionStepAndProcess(transitionExecution, outcome, onEvent)
    } yield ()

  private def runInParallel(tasks: List[F[Unit]])(implicit async: AsyncSupport[F]): F[Unit] =
    tasks match {
      case Nil =>
        async.unit
      case _ =>
        for {
          remaining <- async.delay(new AtomicInteger(tasks.size))
          done <- async.delay(new CompletableFuture[Unit]())
          _ <- tasks.foldLeft(async.unit) { (acc, task) =>
            acc.flatMap(_ => {
              val wrappedTask =
                async.attempt(task).flatMap {
                  case Left(error) =>
                    async.delay(done.completeExceptionally(error)).map(_ => ())
                  case Right(_) =>
                    async.delay {
                      if (remaining.decrementAndGet() == 0) done.complete(())
                    }.map(_ => ())
                }
              async.startAndForget(wrappedTask)
            })
          }
          _ <- async.fromCompletableFuture(async.delay(done))
        } yield ()
    }

  /** The "induction step" is the "repeating" 2nd, 3rd... nth step in transition execution.
    *
    * This executes enabled transitions depth-first and emits events through the callback.
    */
  private def inductionStepAndProcess(finishedExecution: TransitionExecution, outcome: TransitionExecution.Outcome, onEvent: EventInstance => F[Unit])(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[Unit] =
    handleExecutionOutcome(finishedExecution)(outcome).flatMap { case (first, enabledExecutions) =>
      val processFirst = first match {
        case Some(output) => onEvent(output)
        case None => async.unit
      }
      val enabledTasks = enabledExecutions.toList.map { enabled =>
        enabled.execute.flatMap(enabledOutcome => inductionStepAndProcess(enabled, enabledOutcome, onEvent))
      }
      processFirst.flatMap(_ => runInParallel(enabledTasks))
    }

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