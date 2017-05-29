package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.compiledRecipe.petrinet.ProvidesType.{ProvidesEvent, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.core.ProcessState

object EventSource {

  def updateIngredientState[I](interactionTransition: InteractionTransition[I], ingredientExtractor: IngredientExtractor): (ProcessState) => (Any) => ProcessState =
    state =>
      event => {
        interactionTransition.providesType match {
          case _ if event == null => state
          case ProvidesIngredient(outputIngredient: (String, Class[_]), _) =>
            state.copy(ingredients = state.ingredients + (outputIngredient._1 -> event))
          case ProvidesEvent(_, _, _) =>
            state.copy(ingredients = state.ingredients ++ ingredientExtractor.extractIngredientData(event))
          case ProvidesNothing => state
          case _ => state
        }
      }

  def updateEventState[T](eventTransition: EventTransition[T], ingredientExtractor: IngredientExtractor): (ProcessState) => (Any) => ProcessState =
    state =>
      event => {
          val eventIngredients = ingredientExtractor.extractIngredientData(event)
          state.copy(ingredients = state.ingredients ++ eventIngredients)
      }
}
