package com.ing.baker.runtime.petrinet

import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, Transition}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}

object RecipeRuntime {
  def eventSourceFn: Transition[_, _] => (ProcessState => RuntimeEvent => ProcessState) =
    _ => state => {
      case null => state
      case RuntimeEvent(name, providedIngredients) => state.copy(ingredients = state.ingredients ++ providedIngredients, eventNames = state.eventNames :+ name)
    }
}

class RecipeRuntime(recipeName: String, interactionManager: InteractionManager) extends PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] {

  override val tokenGame = new RecipeTokenGame()

  override val eventSourceFn: Transition[_, _] => (ProcessState => RuntimeEvent => ProcessState) = RecipeRuntime.eventSourceFn

  override val exceptionHandlerFn: Transition[_, _] => TransitionExceptionHandler[Place] = {
    case interaction: InteractionTransition[_] =>
      {
        case (_: Error, _, _) => BlockTransition
        case (_, n, outMarking) => {
          interaction.failureStrategy.apply(n) match {
            case ExceptionStrategyOutcome.BlockTransition => BlockTransition
            case ExceptionStrategyOutcome.RetryWithDelay(delay) => RetryWithDelay(delay)
            case ExceptionStrategyOutcome.Continue(eventType) => {
              val runtimeEvent = new RuntimeEvent(eventType.name, Seq.empty)
              Continue(createProducedMarking(interaction, outMarking)(runtimeEvent), runtimeEvent)
            }
          }
        }
      }
    case _ => (_, _, _) => BlockTransition
  }

  override val taskProvider = new TaskProvider(recipeName, interactionManager)

  override lazy val jobPicker = new JobPicker[Place, Transition](tokenGame) {
    override def isAutoFireable[S](instance: Instance[Place, Transition, S], t: Transition[_, _]): Boolean = t match {
      case EventTransition(_, true, _) => false
      case _ => true
    }
  }
}
