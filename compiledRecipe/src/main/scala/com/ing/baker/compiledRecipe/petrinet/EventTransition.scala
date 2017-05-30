package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.core.ProcessState

/**
  * Transition providing data from an event.
  *
  * @param clazz The event class
  * @tparam E The type of the event
  */
case class EventTransition[E](clazz: Class[E],
                              val isSensoryEvent: Boolean = true,
                              val isMissing: Boolean = false) extends Transition[Unit, E, ProcessState] {

  override val id       = (clazz.getName + "EventTransition").hashCode.toLong
  override val label    = clazz.getSimpleName
  override val toString = label

  // TODO move once refactor complete
//  def produceEvent(consume: Marking[Place], state: ProcessState, input: E): Task[E] = Task.now(input)
//  def updateState = state => e => {
//      val eventIngredients = ingredientExtractor.extractIngredientData(e.asInstanceOf[AnyRef])
//      state.copy(ingredients = state.ingredients ++ eventIngredients)
//  }
}
