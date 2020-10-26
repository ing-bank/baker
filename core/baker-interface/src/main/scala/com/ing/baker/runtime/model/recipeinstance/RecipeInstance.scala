package com.ing.baker.runtime.model.recipeinstance

import cats.data.EitherT
import cats.effect.{Clock, ConcurrentEffect, Sync}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FireTransitionValidation
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.types.Value

case class RecipeInstance(
                           recipeInstanceId: String,
                           recipe: CompiledRecipe,
                           sequenceNumber: Long,
                           marking: Marking[Place],
                           ingredients: Map[String, Value],
                           events: List[(EventInstance, Long)],
                           executions: Map[Long, TransitionExecution],
                           receivedCorrelationIds: Set[String],
                           createdOn: Long
                         ) extends RecipeInstanceUtils { self =>

  /** Validates an attempt to fire an event, and if valid it suspends the effect of such action.
    * As well returns an updated version of the RecipeInstance.
    *
    * Note that the execution effect is still suspended and should be run on due time to move the recipe instance state
    * forward with the resulting TransitionExecutionOutcome.
    *
    * @param input
    * @param correlationId
    * @param components
    * @param effect
    * @param clock
    * @return The returning type is either a validation rejection with its explanation, or an updated state of the recipe
    *         instance with the encapsulated effect of firing the event.
    */
  def fire[F[_]](input: EventInstance, correlationId: Option[String] = None)(implicit components: BakerComponents[F], effect: Sync[F], clock: Clock[F]): FireTransitionValidation[F, (RecipeInstance, F[TransitionExecutionOutcome])] = {
    for {
      firing <- validateInputAndCreateExecution(input, correlationId)
      updatedInstance = addExecution(firing)
    } yield updatedInstance -> firing.execute
  }

  /** Attempts to progress the execution of the recipe instance, by finding and executing any enabled events or interactions.
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
  def step[F[_]](implicit components: BakerComponents[F], effect: ConcurrentEffect[F], clock: Clock[F]): (RecipeInstance, Seq[F[TransitionExecutionOutcome]]) = {
    val enabledExecutions = allEnabledExecutions
    addExecution(enabledExecutions: _*) -> enabledExecutions.map(_.execute)
  }

}

object RecipeInstance {

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)

  type Reason = String

  type FireTransitionValidation[F[_], A] =
    EitherT[F, (FireSensoryEventRejection, Reason), A]

  def empty(recipe: CompiledRecipe, recipeInstanceId: String, createdOn: Long): RecipeInstance =
    RecipeInstance(
      recipe = recipe,
      marking = recipe.initialMarking,
      sequenceNumber = 0,
      recipeInstanceId = recipeInstanceId,
      ingredients = Map.empty,
      events = List.empty,
      executions = Map.empty,
      receivedCorrelationIds = Set.empty,
      createdOn = createdOn
    )
}
