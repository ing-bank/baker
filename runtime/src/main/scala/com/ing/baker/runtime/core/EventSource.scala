package com.ing.baker.runtime.core

import com.ing.baker.compiledRecipe.petrinet.EventTransition
import com.ing.baker.core.ProcessState
import org.slf4j.LoggerFactory

object EventSource {

  private val log = LoggerFactory.getLogger("com.ing.baker.compiledRecipe.petrinet.EventSource")

  def updateStateFromInteractionOutput(): (ProcessState) => (RuntimeEvent) => ProcessState =
    state => (event: RuntimeEvent) => state.copy(ingredients = state.ingredients ++ event.providedIngredients)


  //Only extract ingredients if they are fired by a sensory events
  //If it is a interaction provided event then the ingredients are provided by the Interaction.
  def updateStateFromEventOutput(eventTransition: EventTransition): (ProcessState) => (RuntimeEvent) => ProcessState =
    state => event =>
      if (eventTransition.isSensoryEvent) state.copy(ingredients = state.ingredients ++ event.providedIngredients)
      else state
}
