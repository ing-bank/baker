package com.ing.baker.runtime.petrinet

import java.lang.reflect.InvocationTargetException

import akka.event.EventStream
import cats.effect.IO
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, Transition}
import com.ing.baker.il.{IngredientDescriptor, processIdName}
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.core.events.{BakerEventBus, InteractionCompleted, InteractionFailed, InteractionStarted}
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}
import com.ing.baker.types.{PrimitiveValue, Value}
import org.slf4j.{LoggerFactory, MDC}

import scala.util.{Failure, Success, Try}

class TaskProvider(recipeName: String, interactionManager: InteractionManager, eventStream: EventStream) extends TransitionTaskProvider[ProcessState, Place, Transition] {

  val log = LoggerFactory.getLogger(classOf[TaskProvider])

  override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] = {
    t match {
      case interaction: InteractionTransition[_] =>
        interactionTransitionTask[AnyRef, Input, Output](interaction.asInstanceOf[InteractionTransition[AnyRef]], petriNet.outMarking(interaction))
      case t: EventTransition  => eventTransitionTask(petriNet, t)
      case t                   => passThroughTransitionTask(petriNet, t)
    }
  }

  def passThroughTransitionTask[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] =
    (_, _, _) => IO.pure((toMarking[Place](petriNet.outMarking(t)), null.asInstanceOf[Output]))

  def eventTransitionTask[RuntimeEvent, Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], eventTransition: EventTransition): TransitionTask[Place, Input, Output, ProcessState] =
    (_, _, input) => IO.pure((toMarking[Place](petriNet.outMarking(eventTransition)), input.asInstanceOf[Output]))

  // function that (optionally) transforms the output event using the event output transformers
  def transformEvent[I](interaction: InteractionTransition[I])(runtimeEvent: RuntimeEvent): RuntimeEvent = {
    interaction.eventOutputTransformers
      .find { case (eventName, _) => runtimeEvent.name.equals(eventName) } match {
      case Some((_, eventOutputTransformer)) =>
        RuntimeEvent(
          eventOutputTransformer.newEventName,
          runtimeEvent.providedIngredients.map { case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
      case None => runtimeEvent
    }
  }

  def interactionTransitionTask[I, Input, Output](interaction: InteractionTransition[I],
                                                  outAdjacent: MultiSet[Place[_]]): TransitionTask[Place, Input, Output, ProcessState] =

    (_, processState, _) => {

      // returns a delayed task that will get executed by the baker petrinet runtime
      IO {

        // add MDC values for logging
        MDC.put("processId", processState.processId)
        MDC.put("recipeName", recipeName)

        // obtain the interaction implementation
        val implementation = interactionManager.get(interaction).getOrElse {
          throw new FatalInteractionException("No implementation available for interaction")
        }

        // create the interaction input
        val input = createInput(interaction, processState)

        // publish the fact that we started the interaction
        eventStream.publish(InteractionStarted(System.currentTimeMillis(), processState.processId, interaction.interactionName))

        Try {
          implementation.execute(interaction, input)
        } match {
          case Failure(e) =>

            eventStream.publish(InteractionFailed(System.currentTimeMillis(), processState.processId, interaction.interactionName, e))

            // remove the MDC values
            MDC.remove("processId")
            MDC.remove("recipeName")

            throw e;
          case Success(interactionOutput) =>

            val (outputEvent, output) = interactionOutput match {
              case None =>
                (RuntimeEvent.create(interaction.interactionName, Seq.empty), null.asInstanceOf[Output])

              case Some(event) =>
                // check if no null ingredients are provided
                val nullIngredients = event.providedIngredients.collect {
                  case (name, null) => s"null value provided for ingredient: $name"
                }

                if (nullIngredients.nonEmpty)
                  throw new FatalInteractionException(nullIngredients.mkString(","))

                // transforms the event
                val transformedEvent = transformEvent(interaction)(event)

                (transformedEvent, transformedEvent.asInstanceOf[Output])
            }

            // publish the fact that the interaction completed
            eventStream.publish(InteractionCompleted(System.currentTimeMillis(), processState.processId, interaction.interactionName, outputEvent))

            // create the output marking for the petri net
            val outputMarking = createProducedMarking(interaction, outAdjacent)(outputEvent)

            // remove the MDC values
            MDC.remove("processId")
            MDC.remove("recipeName")

            (outputMarking, output)
        }

      }.handleWith {
        case e: InvocationTargetException => IO.raiseError(e.getCause)
        case e: Throwable                 => IO.raiseError(e)
      }
    }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createInput[A](interaction: InteractionTransition[A], state: ProcessState): Seq[Value] = {

    // We do not support any other type then String types
    val processId: (String, Value) = processIdName -> PrimitiveValue(state.processId.toString)

    // parameterNamesToValues overwrites mapped token values which overwrites context map (in order of importance)
    val argumentNamesToValues: Map[String, Value] = interaction.predefinedParameters ++ state.ingredients + processId

    def throwMissingInputException = (name: String) => {
      val msg =
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Required input   : ${interaction.requiredIngredients.mkString(",")}
           |Provided input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin
      log.warn(msg)
      throw new IllegalArgumentException(msg)
    }

    // map the values to the input places, throw an error if a value is not found
    val interactionInput: Seq[Value] =
      interaction.requiredIngredients.map {
        case IngredientDescriptor(name, _) => argumentNamesToValues.getOrElse(name, throwMissingInputException).asInstanceOf[Value]
      }

    interactionInput
  }
}
