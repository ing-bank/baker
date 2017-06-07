package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.compiledRecipe.RuntimeEvent
import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.core.ProcessState

object EventSource {

  def updateIngredientState[I](interactionTransition: InteractionTransition[I], ingredientExtractor: IngredientExtractor): (ProcessState) => (Any) => ProcessState =
    state =>
      event => {
        interactionTransition.providesType match {
          case _ if event == null => state
          case ProvidesIngredient(ingredient) =>
            state.copy(ingredients = state.ingredients + (ingredient.name -> event))
          case FiresOneOfEvents(events) =>
            state.copy(ingredients = state.ingredients ++ ingredientExtractor.extractIngredientData(event))
          case ProvidesNothing => state
          case _ => state
        }
      }

  def updateEventState(eventTransition: EventTransition, ingredientExtractor: IngredientExtractor): (ProcessState) => (Any) => ProcessState =
    state =>
      event => {
          val eventIngredients = ingredientExtractor.extractIngredientData(event)
          state.copy(ingredients = state.ingredients ++ eventIngredients)
      }
}
