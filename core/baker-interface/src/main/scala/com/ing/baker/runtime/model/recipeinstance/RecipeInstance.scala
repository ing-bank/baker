package com.ing.baker.runtime.model.recipeinstance

import cats.effect.{Clock, Sync}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.{EventStream, InteractionManager}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.types.Value

case class RecipeInstance[F[_]](
    recipeInstanceId: String,
    recipe: CompiledRecipe,
    sequenceNumber: Long,
    marking: Marking[Place],
    ingredients: Map[String, Value],
    events: List[(Int, EventInstance)],
    firings: Map[Long, TransitionFiring[F]],
    receivedCorrelationIds: Set[String],
    interactionManager: InteractionManager[F],
    eventStream: EventStream[F]
  ) { self =>

  def fireTransition(transitionId: Long, input: EventInstance, correlationId: Option[String] = None)(implicit effect: Sync[F], clock: Clock[F]): Either[(FireSensoryEventRejection, String), (RecipeInstance[F], F[TransitionEvent])] = {
    for {
      firing <- TransitionFiring.create(self, transitionId, input, correlationId)
      updatedInstance = copy(firings = firings + (firing.id -> firing))
    } yield updatedInstance -> firing.fire
  }
}

object RecipeInstance {

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String, interactionManager: InteractionManager[F], eventStream: EventStream[F]): RecipeInstance[F] =
    RecipeInstance[F](
      recipe = recipe,
      marking = recipe.initialMarking,
      sequenceNumber = 0,
      recipeInstanceId = recipeInstanceId,
      ingredients = Map.empty,
      events = List.empty,
      firings = Map.empty,
      receivedCorrelationIds = Set.empty,
      interactionManager = interactionManager,
      eventStream = eventStream
    )
}
