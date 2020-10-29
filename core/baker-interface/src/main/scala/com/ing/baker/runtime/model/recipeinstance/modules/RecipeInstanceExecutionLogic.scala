package com.ing.baker.runtime.model.recipeinstance.modules

import cats.effect.concurrent.{Deferred, Ref}
import cats.effect.{Clock, Concurrent, ConcurrentEffect, Sync}
import cats.implicits._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.{RecipeInstance, TransitionExecution, TransitionExecutionOutcome}
import com.ing.baker.runtime.scaladsl.{EventInstance, SensoryEventResult}
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.{Logger, LoggerFactory}

import scala.concurrent.duration.MILLISECONDS

object RecipeInstanceExecutionLogic extends LazyLogging {

  type UpdateHandler[F[_]] = (String, RecipeInstance => RecipeInstance) => F[RecipeInstance]

  private type UpdateHandlerWithRecipeInstanceId[F[_]] = (RecipeInstance => RecipeInstance) => F[RecipeInstance]

  type FireEventExecution[F[_]] = Either[FireSensoryEventRejection, F[Unit]]

  final class EventsLobby[F[_]](lobby: Ref[F, Map[String, Deferred[F, SensoryEventResult]]]) {

    def awaitForEvent(eventName: String)(implicit effect: Concurrent[F]): F[SensoryEventResult] =
      getOrCreateWaitingSpot(eventName).flatMap(_.get)

    def resolveEvent(eventName: String, sensoryEventResult: SensoryEventResult)(implicit effect: Concurrent[F]): F[Unit] =
      getOrCreateWaitingSpot(eventName).flatMap(_.complete(sensoryEventResult))

    def resolveWith(eventName: String, recipeInstance: RecipeInstance)(implicit effect: Concurrent[F]): F[Unit] = {
      val result = SensoryEventResult(
        sensoryEventStatus = SensoryEventStatus.Completed,
        eventNames = recipeInstance.events.map(_.name),
        ingredients = recipeInstance.ingredients
      )
      resolveEvent(eventName, result)
    }

    private def getOrCreateWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] =
      for {
        spots <- lobby.get
        spot <- spots.get(eventName)
          .fold(createWaitingSpot(eventName), effect.pure)
      } yield spot

    private def createWaitingSpot(eventName: String)(implicit effect: Concurrent[F]): F[Deferred[F, SensoryEventResult]] = {
      val newSpot = Deferred[F, SensoryEventResult]
      lobby.update(_ + (eventName -> newSpot)).as(newSpot)
    }
  }

  /** Base case of the recipe instance execution semantics.
    * Validates an attempt to fire an event, and if valid it returns the effect of such action.
    * The returning effect will resolve right after the event has been recorded and is considered received, but
    * asynchronously it cascades the instance execution semantics.
    *
    * @return The returning type is either a validation rejection or the encapsulated effect of firing the event.
    *         Note that the operation is wrapped within an effect because 2 reasons, first, the validation checks for
    *         current time, and second, if there is a rejection a message is logged, both are suspended into F.
    */
  def fire[F[_]](input: EventInstance, recipeInstance: RecipeInstance, correlationId: Option[String] = None)(updateHandler: UpdateHandler[F], eventsLobby: EventsLobby[F])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], clock: Clock[F]): F[FireEventExecution[F]] =
    for {
      currentTime <- clock.realTime(MILLISECONDS)
      firingEffect <- logRejectionReasonIfAny {
        recipeInstance.validateExecution(input, correlationId, currentTime)
          .map { firing =>
            val instanceId = recipeInstance.recipeInstanceId
            updateHandler(instanceId, _.addExecution(firing)) *> step[F](firing, instanceId)(updateHandler, eventsLobby)
          }
      }
    } yield firingEffect

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
  def step[F[_]](execution: TransitionExecution, recipeInstanceId: String)(updateHandler: UpdateHandler[F], eventsLobby: EventsLobby[F])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], clock: Clock[F]): F[Unit] = {

    effect.runAsync(execution.execute)({
      case Right(outcome: TransitionExecutionOutcome.Completed) =>

        // TODO normally here an implementation might do something about it, like doing event sourcing
        // TODO regarding the last TODO, event sourcing could be solved by the onEvent callback together with the recordExecutionOutcome
        for {
          recipeInstance <- updateHandler(recipeInstanceId, _.recordExecutionOutcome(outcome))
          _ <- execution.input.fold(effect.unit)(originalEvent => eventsLobby.resolveWith(originalEvent.name, recipeInstance))
          enabledExecutions = recipeInstance.allEnabledExecutions
          _ <- updateHandler(recipeInstanceId, _.addExecution(enabledExecutions: _*))
          _ <- enabledExecutions.toList.traverse(step[F](_, recipeInstanceId)(updateHandler, eventsLobby))
        } yield ()
        ???
      case Right(outcome: TransitionExecutionOutcome.Failed) =>
        // TODO handle failed interaction, equivalent to TransitionFailedEvent on the process instance actor
        ???
      case Left(e) =>
        val message =
            """
            |Unexpected exception when firing an event, it should be impossible to have exceptions at this point.
            |The execution.execute should wrap any exception from interaction instances and report them as failed outcomes.
            |""".stripMargin
        val exception = new IllegalStateException(message, e)
        effect.delay(logger.error(message, exception))
    }).to[F]
  }

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
