package com.ing.baker.runtime.model.recipeinstance

import cats.data.EitherT
import cats.effect.{Timer, ConcurrentEffect, IO}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.modules._
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment}
import com.ing.baker.types.Value
import com.typesafe.scalalogging.{LazyLogging, Logger}

case class RecipeInstance(
                           recipeInstanceId: String,
                           recipe: CompiledRecipe,
                           sequenceNumber: Long,
                           marking: Marking[Place],
                           ingredients: Map[String, Value],
                           events: List[EventMoment],
                           executions: Map[Long, TransitionExecution],
                           runningExecutions: Map[Long, TransitionExecution],
                           receivedCorrelationIds: Set[String],
                           createdOn: Long
                         )
  extends RecipeInstanceComplexProperties
    with RecipeInstanceEventValidation
    with RecipeInstanceStateMutations
    with LazyLogging {

  /** Base case of the recipe instance execution semantics.
    * Validates an attempt to fire an event, and if valid it returns the effect of such action.
    * The returning effect will resolve right after the event has been recorded and is considered received, but
    * asynchronously it cascades the instance execution semantics.
    *
    * @return The returning type is either a validation rejection or the encapsulated effect of firing the event.
    *         Note that the operation is wrapped within an effect because 2 reasons, first, the validation checks for
    *         current time, and second, if there is a rejection a message is logged, both are suspended into F.
    */
  def fire[F[_]](input: EventInstance, correlationId: Option[String])(eventsLobby: EventsLobby[F], updateInstance: RecipeInstance.UpdateHandler[F])(implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]): EitherT[F, FireSensoryEventRejection, RecipeInstance.FireEventExecution[F]] =
    RecipeInstanceExecutionLogic.fire(input, recipeInstance = this, correlationId, eventsLobby, updateInstance)
}

object RecipeInstance {

  type UpdateHandler[F[_]] = (String, RecipeInstance => RecipeInstance) => F[RecipeInstance]

  type FireEventExecution[F[_]] = F[Unit]

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)

  def logImpossibleException(logger: Logger, cause: Throwable): IO[Unit] = {
    val message = """Imminent bug, unexpected exception when firing an event, it should be impossible to have exceptions at this point.
                    |The execution.execute should wrap any exception from interaction instances and report them as failed outcomes.
                    |The process of firing an event is free of exceptions besides the previously mentioned, this is used to properly
                    |implement the cats effect ConcurrentEffect.runAsync method.
                    |""".stripMargin
    IO.delay(logger.error(message, new IllegalStateException(message, cause)))
  }

  def empty(recipe: CompiledRecipe, recipeInstanceId: String, createdOn: Long): RecipeInstance =
    RecipeInstance(
      recipe = recipe,
      marking = recipe.initialMarking,
      sequenceNumber = 0,
      recipeInstanceId = recipeInstanceId,
      ingredients = Map.empty,
      events = List.empty,
      executions = Map.empty,
      runningExecutions = Map.empty,
      receivedCorrelationIds = Set.empty,
      createdOn = createdOn
    )
}
