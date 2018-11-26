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
      case interaction: InteractionTransition => interactionTask(interaction, petriNet.outMarking(t), state)
      case t: EventTransition                 => IO.pure(petriNet.outMarking(t).toMarking, input.asInstanceOf[RuntimeEvent])
      case t                                  => IO.pure(petriNet.outMarking(t).toMarking, null.asInstanceOf[RuntimeEvent])
    }
  }

  /**
    * Creates the input parameters for an interaction implementation
    */
  def createInput(interaction: InteractionTransition, state: ProcessState): Seq[Value] = {

    // the process id is a special ingredient that is always available
    val processId: (String, Value) = processIdName -> PrimitiveValue(state.processId.toString)

    // a map of all ingredients
    val allIngredients: Map[String, Value] = interaction.predefinedParameters ++ state.ingredients + processId

    // arranges the ingredients in the expected order
    interaction.requiredIngredients.map {
      case IngredientDescriptor(name, _) =>
        allIngredients.getOrElse(name, throw new FatalInteractionException(s"Missing parameter '$name'"))
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
        // an event was expected but none was provided
        if (!interaction.eventsToFire.isEmpty)
          throw new FatalInteractionException(s"Interaction '${interaction.interactionName}' did not provide any output, expected one of: ${interaction.eventsToFire.map(_.name).mkString(",")}")

      case Some(event) =>

        val nullIngredientNames = event.providedIngredients.collect {
          case (name, null) => name
        }

        // null values for ingredients are NOT allowed
        if(nullIngredientNames.nonEmpty)
          throw new FatalInteractionException(s"Interaction '${interaction.interactionName}' returned null for the following ingredients: ${nullIngredientNames.mkString(",")}")

        // the event name must match an event name from the interaction output
        interaction.originalEvents.find(_.name == event.name) match {
          case None =>
            throw new FatalInteractionException(s"Interaction '${interaction.interactionName}' returned unkown event '${event.name}, expected one of: ${interaction.eventsToFire.map(_.name).mkString(",")}")
          case Some(eventType) =>
            val errors = event.validateEvent(eventType)

            if (errors.nonEmpty)
              throw new FatalInteractionException(s"Event '${event.name}' does not match the expected type: ${errors.mkString}")
        }
    }
  }

  def interactionTask(interaction: InteractionTransition,
                      outAdjacent: MultiSet[Place],
                      processState: ProcessState): IO[(Marking[Place], RuntimeEvent)] = {

      // returns a delayed task that will get executed by the process instance
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
          val outputMarking: Marking[Place] = RecipeRuntime.createProducedMarking(outAdjacent, outputEvent)

          (outputMarking, outputEvent.orNull)

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
}
