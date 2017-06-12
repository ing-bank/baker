package com.ing.baker.runtime

import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.compiledRecipe.petrinet.{EventTransition, InteractionTransition, Place, RecipePetriNet, RecipeTokenGame, Transition}
import com.ing.baker.core.ProcessState
import fs2.Strategy
import io.kagera.execution.ExceptionStrategy.BlockTransition
import io.kagera.execution._

package object core {
  val jobPicker = new JobPicker[Place, Transition](new RecipeTokenGame()) {
    override def isFireable[S](instance: Instance[Place, Transition, S], t: Transition[_, _, _]): Boolean = t match {
      case EventTransition(_, isSensoryEvent, _) => !isSensoryEvent
      case _ => true
    }
  }

  def transitionEventSource(ingredientExtractor: IngredientExtractor): Transition[_,_,_] => (ProcessState => RuntimeEvent => ProcessState) = {
    case t: InteractionTransition[_] => EventSource.updateStateFromInteractionOutput()
    case t: EventTransition          => EventSource.updateStateFromEventOutput(t)
    case t                           => EventSource.updateNothing()
  }


  val transitionExceptionHandler: Transition[_,_,_] => TransitionExceptionHandler = {
    case interaction: InteractionTransition[_] => interaction.exceptionStrategy
    case _ => (e, n) => BlockTransition
  }

  def jobExecutor(topology: RecipePetriNet, interactions: Map[String, () => AnyRef], ingredientExtractor: IngredientExtractor, evaluationStrategy: Strategy) =
    new JobExecutor[ProcessState, Place, Transition](topology, new TaskProvider(interactions, ingredientExtractor), transitionExceptionHandler)(evaluationStrategy)
}
