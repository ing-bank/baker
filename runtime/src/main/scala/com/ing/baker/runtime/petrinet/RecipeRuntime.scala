package com.ing.baker.runtime.petrinet

import com.ing.baker.il.petrinet.{InteractionTransition, Place, Transition}
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime._

class RecipeRuntime(interactionFunctions: InteractionTransition[_] => (ProcessState => RuntimeEvent)) extends PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] {

  override val tokenGame = new RecipeTokenGame()

  override val eventSourceFn: Transition[_, _] => (ProcessState => RuntimeEvent => ProcessState) =
    _ => state => {
      case null => state
      case RuntimeEvent(_, providedIngredients) => state.copy(ingredients = state.ingredients ++ providedIngredients)
    }

  override val exceptionHandlerFn: Transition[_, _] => TransitionExceptionHandler = {
    case interaction: InteractionTransition[_] => interaction.exceptionStrategy
    case _ => (_, _) => BlockTransition
  }

  override val taskProvider = new TaskProvider(interactionFunctions)
}
