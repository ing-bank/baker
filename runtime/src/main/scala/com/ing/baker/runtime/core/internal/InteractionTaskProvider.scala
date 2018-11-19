package com.ing.baker.runtime.core.internal

import java.lang.reflect.InvocationTargetException

import akka.event.EventStream
import cats.effect.IO
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, Transition}
import com.ing.baker.il.{CompiledRecipe, IngredientDescriptor, processIdName}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.core.events.{InteractionCompleted, InteractionStarted}
import com.ing.baker.runtime.core._
import com.ing.baker.types.{PrimitiveValue, Value}
import org.slf4j.{LoggerFactory, MDC}

class InteractionTaskProvider(recipe: CompiledRecipe, interactionManager: InteractionManager, eventStream: EventStream) {

  val log = LoggerFactory.getLogger(classOf[InteractionTaskProvider])

  def apply(petriNet: PetriNet[Place, Transition], t: Transition)(marking: Marking[Place], state: ProcessState, input: Any): IO[(Marking[Place], RuntimeEvent)] = {
    t match {
      case interaction: InteractionTransition => interactionTransitionTask(interaction, petriNet.outMarking(t), state)
      case t: EventTransition                 => IO.pure(petriNet.outMarking(t).toMarking, input.asInstanceOf[RuntimeEvent])
      case t                                  => IO.pure(petriNet.outMarking(t).toMarking, null.asInstanceOf[RuntimeEvent])
    }
  }

  // function that (optionally) transforms the output event using the event output transformers
  def transformEvent(interaction: InteractionTransition, runtimeEvent: RuntimeEvent): RuntimeEvent = {
    interaction.eventOutputTransformers
      .find { case (eventName, _) => runtimeEvent.name.equals(eventName) } match {
      case Some((_, eventOutputTransformer)) =>
        RuntimeEvent(
          eventOutputTransformer.newEventName,
          runtimeEvent.providedIngredients.map { case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
      case None => runtimeEvent
    }
  }

  /**
    * Validates the output event of an interaction
    *
    * @throws FatalInteractionException If the event was invalid.
    */
  def validateEvent(interaction: InteractionTransition, optionalEvent: Option[RuntimeEvent]) = {

    optionalEvent match {

      case None =>
        if (!interaction.eventsToFire.isEmpty)
          throw new FatalInteractionException(s"Interaction ${interaction.interactionName} did not provide an output")

      case Some(event) =>

        val nullIngredientNames = event.providedIngredients.collect {
          case (name, null) => name
        }

        // null values for ingredients are not allowed
        if(nullIngredientNames.nonEmpty)
          throw new FatalInteractionException(s"Interaction ${interaction.interactionName} returned null value for ingredients: ${nullIngredientNames.mkString(",")}")

        // the event name must match an event name from the interaction output
        interaction.originalEvents.find(_.name == event.name) match {
          case None =>
            throw new FatalInteractionException(s"No event with name '${event.name}' is known by this interaction")
          case Some(eventType) =>
            val errors = event.validateEvent(eventType)

            if (errors.nonEmpty)
              throw new FatalInteractionException(s"Event '${event.name}' does not match the expected type: ${errors.mkString}")
        }
    }
  }

  def interactionTransitionTask(interaction: InteractionTransition,
                                outAdjacent: MultiSet[Place],
                                processState: ProcessState): IO[(Marking[Place], RuntimeEvent)] = {

      // returns a delayed task that will get executed by the baker petrinet runtime
      IO {

        // add MDC values for logging
        MDC.put("processId", processState.processId)
        MDC.put("recipeName", recipe.name)

        try {

          // obtain the interaction implementation
          val implementation = interactionManager.getImplementation(interaction).getOrElse {
            throw new FatalInteractionException("No implementation available for interaction")
          }

          // create the interaction input
          val input = createInput(interaction, processState)

          val timeStarted = System.currentTimeMillis()

          // publish the fact that we started the interaction
          eventStream.publish(InteractionStarted(timeStarted, recipe.name, recipe.recipeId, processState.processId, interaction.interactionName))

          // executes the interaction and obtain the (optional) output event
          val interactionOutput: Option[RuntimeEvent] = implementation.execute(input)

          // validates the event, throws a FatalInteraction exception if invalid
          validateEvent(interaction, interactionOutput)

          // transform the event if there is one
          val outputEvent: Option[RuntimeEvent] = interactionOutput
            .map(e => transformEvent(interaction, e))

          val timeCompleted = System.currentTimeMillis()

          // publish the fact that the interaction completed
          eventStream.publish(InteractionCompleted(timeCompleted, timeCompleted - timeStarted, recipe.name, recipe.recipeId, processState.processId, interaction.interactionName, outputEvent))

          // create the output marking for the petri net
          val outputMarking: Marking[Place] = RecipeRuntime.createProducedMarking(interaction, outAdjacent, outputEvent)

          (outputMarking, outputEvent.getOrElse(null))

        } finally {
          // remove the MDC values
          MDC.remove("processId")
          MDC.remove("recipeName")
        }

      }.handleExceptionWith {
        case e: InvocationTargetException => IO.raiseError(e.getCause)
        case e: Throwable                 => IO.raiseError(e)
      }
    }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createInput(interaction: InteractionTransition, state: ProcessState): Seq[Value] = {

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
