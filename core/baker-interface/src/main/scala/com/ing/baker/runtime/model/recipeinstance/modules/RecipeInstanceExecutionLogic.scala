package com.ing.baker.runtime.model.recipeinstance.modules

import cats.data.EitherT
import cats.effect.{Clock, ConcurrentEffect, IO, Sync}
import cats.implicits._
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.{EventsLobby, RecipeInstance, TransitionExecution, TransitionExecutionOutcome}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.{Logger, LoggerFactory}

import scala.concurrent.duration.MILLISECONDS

object RecipeInstanceExecutionLogic extends LazyLogging {

  /** Base case of the recipe instance execution semantics.
    * Validates an attempt to fire an event, and if valid it returns the effect of such action.
    * The returning effect will resolve right after the event has been recorded and is considered received, but
    * asynchronously it cascades the instance execution semantics.
    *
    * @return The returning type is either a validation rejection or the encapsulated effect of firing the event.
    *         Note that the operation is wrapped within an effect because 2 reasons, first, the validation checks for
    *         current time, and second, if there is a rejection a message is logged, both are suspended into F.
    */
  def fire[F[_]](input: EventInstance,
                 recipeInstance: RecipeInstance,
                 correlationId: Option[String],
                 eventsLobby: EventsLobby[F],
                 updateInstance: RecipeInstance.UpdateHandler[F]
                )(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], clock: Clock[F]): EitherT[F, FireSensoryEventRejection, RecipeInstance.FireEventExecution[F]] =
    EitherT(for {
      currentTime <- clock.realTime(MILLISECONDS)
      firingEffect <- logRejectionReasonIfAny {
        recipeInstance.validateExecution(input, correlationId, currentTime)
          .map { firing =>
            val instanceId = recipeInstance.recipeInstanceId
            updateInstance(instanceId, _.addExecution(firing)) *> step[F](firing, instanceId, eventsLobby, updateInstance)
          }
      }
    } yield firingEffect)

  /** Inductive step of the recipe instance execution semantics.
    * Attempts to progress the execution of the recipe instance from the outcome of a previous execution.
    *
    * Note that the execution effects are still suspended and should be run on due time to move the recipe instance state
    * forward with the resulting TransitionExecutionOutcome.
    *
    * @param components
    * @param effect
    * @param clock
    * @tparam F
    * @return
    */
  private def step[F[_]](execution: TransitionExecution,
                 recipeInstanceId: String,
                 eventsLobby: EventsLobby[F],
                 updateInstance: RecipeInstance.UpdateHandler[F]
                )(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], clock: Clock[F]): F[Unit] = {
    effect.runAsync(execution.execute) {

      case Right(outcome: TransitionExecutionOutcome.Completed) =>
        effect.toIO(handleCompletedOutcome(execution.input, outcome, recipeInstanceId, eventsLobby, updateInstance))

      case Right(outcome: TransitionExecutionOutcome.Failed) =>
        // TODO handle failed interaction, equivalent to TransitionFailedEvent on the process instance actor
        ???

      case Left(e) =>
        RecipeInstance.logImpossibleException(logger, e)
    }.to[F]
  }

  private def handleCompletedOutcome[F[_]](originalInput: Option[EventInstance],
                                           outcome: TransitionExecutionOutcome.Completed,
                                           recipeInstanceId: String,
                                           eventsLobby: EventsLobby[F],
                                           updateInstance: RecipeInstance.UpdateHandler[F]
                                          )(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], clock: Clock[F]): F[Unit] =
    for {
      recipeInstance <- updateInstance(recipeInstanceId, _.recordExecutionOutcome(outcome))
      _ <- originalInput.fold(effect.unit)(originalEvent => eventsLobby.resolveWith(originalEvent.name, recipeInstance))
      enabledExecutions = recipeInstance.allEnabledExecutions
      _ <- updateInstance(recipeInstanceId, _.addExecution(enabledExecutions: _*))
      _ <- enabledExecutions.toList.traverse(step[F](_, recipeInstanceId, eventsLobby, updateInstance))
    } yield ()

  /** Helper function to log and remove the textual rejection reason of the `fire` operation. It basically exchanges the
    * String inside the returning `Either` for an external effect `F`.
    *
    * @param validation
    * @param effect
    * @tparam F
    * @return
    */
  private def logRejectionReasonIfAny[F[_]](validation: Either[(FireSensoryEventRejection, String), F[Unit]])(implicit effect: Sync[F]): F[Either[FireSensoryEventRejection, F[Unit]]] = {
    // TODO relate this to the recipe instance logger
    val log: Logger = LoggerFactory.getLogger("com.ing.baker.runtime.model.recipeinstance.RecipeInstance")
    validation match {
      case Left((rejection, reason)) =>
        effect.delay(log.info(s"Event rejected: $reason"))
          .as(Left(rejection))
      case Right(event) =>
        effect.pure(Right(event))
    }
  }
}
