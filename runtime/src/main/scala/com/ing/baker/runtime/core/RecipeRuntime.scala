package com.ing.baker.runtime.core

import com.ing.baker.il.petrinet.{InteractionTransition, Place, Transition}
import io.kagera.runtime.ExceptionStrategy.BlockTransition
import io.kagera.runtime._

class RecipeRuntime(interactionFunctions: InteractionTransition[_] => (ProcessState => RuntimeEvent)) extends PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] {

  override val tokenGame = new RecipeTokenGame()

  override val eventSourceFn: Transition[_,_] => (ProcessState => RuntimeEvent => ProcessState) = t => state => {
      case null                                    => state
      case RuntimeEvent(name, providedIngredients) => state.copy(ingredients = state.ingredients ++ providedIngredients)
    }

  override val exceptionHandlerFn: Transition[_,_] => TransitionExceptionHandler = {
    case interaction: InteractionTransition[_] => interaction.exceptionStrategy
    case _                                     => (e, n) => BlockTransition
  }

  override val taskProvider = new TaskProvider(interactionFunctions)
}
