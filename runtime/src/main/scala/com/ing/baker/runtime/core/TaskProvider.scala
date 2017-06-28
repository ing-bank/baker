package com.ing.baker.runtime.core

import java.lang.reflect.InvocationTargetException
import java.util.UUID

import com.ing.baker.il._
import com.ing.baker.il.petrinet.{EventTransition, FiresOneOfEvents, InteractionTransition, Place, ProvidesIngredient, ProvidesNothing, Transition}
import fs2.Task
import io.kagera.api._
import io.kagera.runtime.{TransitionTask, TransitionTaskProvider}
import org.slf4j.{LoggerFactory, MDC}

import scala.util.Try

class TaskProvider(interactionFunctions: InteractionTransition[_] => (ProcessState => RuntimeEvent)) extends TransitionTaskProvider[ProcessState, Place, Transition] {

  val log = LoggerFactory.getLogger(classOf[TaskProvider])

  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking

  override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] = {
    t match {
      case interaction: InteractionTransition[_] =>
        interactionTransitionTask[AnyRef, Input, Output](interaction.asInstanceOf[InteractionTransition[AnyRef]], interactionFunctions(interaction), petriNet.outMarking(interaction))
      case t: EventTransition  => eventTransitionTask(petriNet, t)
      case t                   => passThroughTransitionTask(petriNet, t)
    }
  }

  def passThroughTransitionTask[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] =
    (consume, processState, input) => Task.now((toMarking[Place](petriNet.outMarking(t)), null.asInstanceOf[Output]))

  def eventTransitionTask[RuntimeEvent, Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], eventTransition: EventTransition): TransitionTask[Place, Input, Output, ProcessState] =
    (consume, processState, input) => Task.now((toMarking[Place](petriNet.outMarking(eventTransition)), input.asInstanceOf[Output]))

  // function that (optionally) transforms the output event using the event output transformers
  def transformEvent[I](interaction: InteractionTransition[I])(runtimeEvent: RuntimeEvent): RuntimeEvent = {
    interaction.providesType match {
      case FiresOneOfEvents(_, _) => {
        interaction.eventOutputTransformers.get(runtimeEvent.toCompiledEvent) match {
          case Some(eventOutputTransformer) =>
            RuntimeEvent(
              eventOutputTransformer.newEventName,
              runtimeEvent.providedIngredients.map{ case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
          case None => runtimeEvent
        }
      }
      case _ => runtimeEvent
    }
  }

  def interactionTransitionTask[I, Input, Output](interaction: InteractionTransition[I], fn: ProcessState => RuntimeEvent, outAdjacent: MultiSet[Place[_]]): TransitionTask[Place, Input, Output, ProcessState] =

    (consume, processState, input) => {

    def failureHandler[T]: PartialFunction[Throwable, Task[T]] = {
      case e: InvocationTargetException => Task.fail(e.getCause)
      case e: Throwable => Task.fail(e)
    }

    Try {
      // returns a delayed task that will get executed by the kagera runtime
      Task
        .delay(fn.apply(processState))
        .map(transformEvent(interaction))
        .map { output => (createProducedMarking(interaction, outAdjacent)(output), output.asInstanceOf[Output]) }
        .handleWith(failureHandler)
    }.recover(failureHandler).get
  }

  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    */
  def createProducedMarking[A](interaction: InteractionTransition[A], outAdjacent: MultiSet[Place[_]]): RuntimeEvent => Marking[Place] = { output =>
    outAdjacent.keys.map { place =>
      val value: Any = {
        interaction.providesType match {
          case FiresOneOfEvents(events, _) =>
            events.find(_.name == output.name).map(_.name).getOrElse {
              throw new IllegalStateException(
                s"Method output: $output is not an instance of any of the specified events: ${
                  events
                    .mkString(",")
                }")
            }
          case _ => ()
        }
      }
      place -> MultiSet(value)
    }.toMarking
  }
}
