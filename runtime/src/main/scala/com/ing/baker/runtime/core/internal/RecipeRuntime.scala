package com.ing.baker.runtime.core.internal

import akka.event.EventStream
import cats.effect.IO
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceRuntime
import com.ing.baker.runtime.actor.process_instance.internal.ExceptionStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.runtime.actor.process_instance.internal._
import com.ing.baker.runtime.core.events.InteractionFailed
import com.ing.baker.runtime.core.internal.RecipeRuntime.createProducedMarking
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}

object RecipeRuntime {
  def eventSourceFn: Transition => (ProcessState => RuntimeEvent => ProcessState) =
    _ => state => {
      case null => state
      case RuntimeEvent(name, providedIngredients) =>
        state.copy(
          ingredients = state.ingredients ++ providedIngredients,
          eventNames = state.eventNames :+ name)
    }

  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    *
    * It fills a token in the out adjacent place of the transition with the interaction name
    */
  def createProducedMarking(outAdjacent: MultiSet[Place], event: Option[RuntimeEvent]): Marking[Place] = {
    outAdjacent.keys.map { place =>

      // use the event name as a token value, otherwise null
      val value: Any = event.map(_.name).getOrElse(null)

      place -> MultiSet.copyOff(Seq(value))
    }.toMarking
  }
}

class RecipeRuntime(recipe: CompiledRecipe, interactionManager: InteractionManager, eventStream: EventStream) extends ProcessInstanceRuntime[Place, Transition, ProcessState, RuntimeEvent] {

  /**
    * All transitions except sensory event interactions are auto-fireable by the runtime
    */
  override def isAutoFireable(instance: Instance[Place, Transition, ProcessState], t: Transition): Boolean = t match {
    case EventTransition(_, true, _) => false
    case _ => true
  }

  /**
    * Tokens which are inhibited by the Edge filter may not be consumed.
    */
  override def consumableTokens(petriNet: PetriNet[Place, Transition])(marking: Marking[Place], p: Place, t: Transition): MultiSet[Any] = {
    val edge = petriNet.findPTEdge(p, t).map(_.asInstanceOf[Edge]).get

    marking.get(p) match {
      case None         ⇒ MultiSet.empty
      case Some(tokens) ⇒ tokens.filter { case (e, _) ⇒ edge.isAllowed(e) }
    }
  }

  override val eventSource = RecipeRuntime.eventSourceFn

  override def handleException(job: Job[Place, Transition, ProcessState])
                              (throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place]): ExceptionStrategy = {

    if (throwable.isInstanceOf[Error])
      BlockTransition
    else
      job.transition match {
        case interaction: InteractionTransition =>

          // compute the interaction failure strategy outcome
          val failureStrategyOutcome = interaction.failureStrategy.apply(failureCount)

          val currentTime = System.currentTimeMillis()

          eventStream.publish(
            InteractionFailed(currentTime, currentTime - startTime, recipe.name, recipe.recipeId,
              job.processState.processId, job.transition.label, failureCount, throwable, failureStrategyOutcome))

          // translates the recipe failure strategy to a petri net failure strategy
          failureStrategyOutcome match {
            case ExceptionStrategyOutcome.BlockTransition => BlockTransition
            case ExceptionStrategyOutcome.RetryWithDelay(delay) => RetryWithDelay(delay)
            case ExceptionStrategyOutcome.Continue(eventName) => {
              val runtimeEvent = RuntimeEvent(eventName, Seq.empty)
              Continue(createProducedMarking(outMarking, Some(runtimeEvent)), runtimeEvent)
            }
          }

        case _ => BlockTransition
      }
  }

  val interactionTaskProvider = new InteractionTaskProvider(recipe, interactionManager, eventStream)

  override def transitionTask(petriNet: PetriNet[Place, Transition], t: Transition)(marking: Marking[Place], state: ProcessState, input: Any): IO[(Marking[Place], RuntimeEvent)] =
    interactionTaskProvider.apply(petriNet, t)(marking, state, input)
}
