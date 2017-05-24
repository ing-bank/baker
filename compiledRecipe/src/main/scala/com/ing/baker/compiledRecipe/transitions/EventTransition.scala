package com.ing.baker.compiledRecipe.transitions

import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.core.ProcessState
import fs2.Task
import io.kagera.api.Marking
import io.kagera.dsl.colored._
import io.kagera.dsl.colored.transitions.UncoloredTransition

/**
  * Transition providing data from an event.
  *
  * @param clazz The event class
  * @tparam E The type of the event
  */
class EventTransition[E](clazz: Class[E], ingredientExtractor: IngredientExtractor) extends UncoloredTransition[E, E, ProcessState] {

  override val id       = clazz.getName.hashCode.toLong
  override val label    = clazz.getSimpleName
  override val toString = label
  override val isAutomated = false

  val providedIngredients = ingredientExtractor.extractIngredientTypes(clazz).keys

  override def produceEvent(consume: Marking[Place], state: ProcessState, input: E): Task[E] = Task.now(input)

  override def updateState = state => e => {
      val eventIngredients = ingredientExtractor.extractIngredientData(e.asInstanceOf[AnyRef])
      state.copy(ingredients = state.ingredients ++ eventIngredients)
  }
}
