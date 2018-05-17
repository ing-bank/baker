package com.ing.baker.runtime.petrinet

import akka.event.EventStream
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, Transition}
import com.ing.baker.petrinet.api.MultiSet
import com.ing.baker.petrinet.runtime.ExceptionStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.core.events.InteractionFailed
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}

object RecipeRuntime {
  def eventSourceFn: Transition[_] => (ProcessState => RuntimeEvent => ProcessState) =
    _ => state => {
      case null => state
      case RuntimeEvent(name, providedIngredients) =>
        state.copy(
          ingredients = state.ingredients ++ providedIngredients,
          eventNames = state.eventNames :+ name)
    }
}

class RecipeRuntime(recipeName: String, interactionManager: InteractionManager, eventStream: EventStream) extends PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] {

  override val tokenGame = new RecipeTokenGame()

  override val eventSource = RecipeRuntime.eventSourceFn

  override val exceptionHandler: ExceptionHandler[Place, Transition, ProcessState] = new ExceptionHandler[Place, Transition, ProcessState] {
    override def handleException(job: Job[Place, Transition, ProcessState])
                                (throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place[_]]) =

      if (throwable.isInstanceOf[Error])
        BlockTransition
      else
        job.transition match {
          case interaction: InteractionTransition[_] =>

            // compute the interaction failure strategy outcome
            val failureStrategyOutcome = interaction.failureStrategy.apply(failureCount)

            val currentTime = System.currentTimeMillis()

            eventStream.publish(
              InteractionFailed(currentTime, currentTime - startTime, recipeName,
                job.processState.processId, job.transition.label, failureCount, throwable, failureStrategyOutcome))

            // translates the recipe failure strategy to a petri net failure strategy
            failureStrategyOutcome match {
              case ExceptionStrategyOutcome.BlockTransition => BlockTransition
              case ExceptionStrategyOutcome.RetryWithDelay(delay) => RetryWithDelay(delay)
              case ExceptionStrategyOutcome.Continue(eventName) => {
                val runtimeEvent = new RuntimeEvent(eventName, Seq.empty)
                Continue(createProducedMarking(interaction, outMarking)(runtimeEvent), runtimeEvent)
              }
            }

          case _ => BlockTransition
        }
  }

  override val taskProvider = new TaskProvider(recipeName, interactionManager, eventStream)

  override lazy val jobPicker = new JobPicker[Place, Transition](tokenGame) {
    override def isAutoFireable[S](instance: Instance[Place, Transition, S], t: Transition[_]): Boolean = t match {
      case EventTransition(_, true, _) => false
      case _ => true
    }
  }
}
