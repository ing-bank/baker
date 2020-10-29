package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.model.recipeinstance.modules._
import com.ing.baker.runtime.scaladsl.EventMoment
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

case class RecipeInstance(
                           recipeInstanceId: String,
                           recipe: CompiledRecipe,
                           sequenceNumber: Long,
                           marking: Marking[Place],
                           ingredients: Map[String, Value],
                           events: List[EventMoment],
                           executions: Map[Long, TransitionExecution],
                           receivedCorrelationIds: Set[String],
                           createdOn: Long
                         )
  extends RecipeInstanceComplexProperties
    with RecipeInstanceEventValidation
    with RecipeInstanceStateMutations
    with LazyLogging

object RecipeInstance {

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)

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
