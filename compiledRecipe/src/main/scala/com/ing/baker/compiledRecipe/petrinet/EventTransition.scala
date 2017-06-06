package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.compiledRecipe.RuntimeEvent
import com.ing.baker.core.ProcessState

/**
  * Transition providing data from an event.
  *
  * @tparam E The type of the event
  */
//TODO remove E since its always RuntimeEvent
case class EventTransition[E <: RuntimeEvent](event: RuntimeEvent,
                              val isSensoryEvent: Boolean = true,
                              val isMissing: Boolean = false) extends Transition[Unit, E, ProcessState] {

  override val id       = (event.name + "EventTransition").hashCode.toLong
  override val label    = event.name
  override val toString = label

  // TODO move once refactor complete
//  def produceEvent(consume: Marking[Place], state: ProcessState, input: E): Task[E] = Task.now(input)
//  def updateState = state => e => {
//      val eventIngredients = ingredientExtractor.extractIngredientData(e.asInstanceOf[AnyRef])
//      state.copy(ingredients = state.ingredients ++ eventIngredients)
//  }
}
