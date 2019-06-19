package com.ing.baker.runtime.akka.internal

import java.lang.reflect.InvocationTargetException

import akka.event.EventStream
import cats.effect.IO
import com.ing.baker.il.{CompiledRecipe, IngredientDescriptor, processIdName}
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceRuntime
import com.ing.baker.runtime.akka.actor.process_instance.internal.ExceptionStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.runtime.akka.actor.process_instance.internal._
import com.ing.baker.runtime.akka.events.{InteractionCompleted, InteractionFailed, InteractionStarted}
import com.ing.baker.runtime.akka.internal.RecipeRuntime._
import com.ing.baker.runtime.scaladsl.ProcessState
import com.ing.baker.runtime.scaladsl.RuntimeEvent
import com.ing.baker.types.{PrimitiveValue, Value}
import org.slf4j.MDC

import scala.concurrent.{ExecutionContext, Future}

object RecipeRuntime {
  def recipeEventSourceFn: Transition => (ProcessState => RuntimeEvent => ProcessState) =
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

  /**
    * Validates the output event of an interaction
    *
    * Returns an optional error message.
    */
  def validateInteractionOutput(interaction: InteractionTransition, optionalEvent: Option[RuntimeEvent]): Option[String] = {

    optionalEvent match {

      // an event was expected but none was provided
      case None =>
        if (!interaction.eventsToFire.isEmpty)
          Some(s"Interaction '${interaction.interactionName}' did not provide any output, expected one of: ${interaction.eventsToFire.map(_.name).mkString(",")}")
        else
          None

      case Some(event) =>

        val nullIngredientNames = event.providedIngredients.collect {
          case (name, null) => name
        }

        // null values for ingredients are NOT allowed
        if(nullIngredientNames.nonEmpty)
          Some(s"Interaction '${interaction.interactionName}' returned null for the following ingredients: ${nullIngredientNames.mkString(",")}")
        else
        // the event name must match an event name from the interaction output
        interaction.originalEvents.find(_.name == event.name) match {
          case None =>
            Some(s"Interaction '${interaction.interactionName}' returned unknown event '${event.name}, expected one of: ${interaction.eventsToFire.map(_.name).mkString(",")}")
          case Some(eventType) =>
            val errors = event.validate(eventType)

            if (errors.nonEmpty)
              Some(s"Event '${event.name}' does not match the expected type: ${errors.mkString}")
            else
              None
        }
    }
  }


  /**
    * Creates the input parameters for an interaction implementation
    */
  def createInteractionInput(interaction: InteractionTransition, state: ProcessState): Map[String, Value] = {

    // the process id is a special ingredient that is always available
    val processId: (String, Value) = processIdName -> PrimitiveValue(state.processId.toString)

    // a map of all ingredients
    val allIngredients: Map[String, Value] = interaction.predefinedParameters ++ state.ingredients + processId

    // arranges the ingredients in the expected order
    interaction.requiredIngredients.map {
      case IngredientDescriptor(name, _) =>
        name -> allIngredients.getOrElse(name, throw new FatalInteractionException(s"Missing parameter '$name'"))
    }.toMap
  }

  // function that (optionally) transforms the output event using the event output transformers
  def transformInteractionEvent(interaction: InteractionTransition, runtimeEvent: RuntimeEvent): RuntimeEvent = {
    interaction.eventOutputTransformers
      .find { case (eventName, _) => runtimeEvent.name.equals(eventName) } match {
      case Some((_, eventOutputTransformer)) =>
        RuntimeEvent(
          eventOutputTransformer.newEventName,
          runtimeEvent.providedIngredients.map { case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
      case None => runtimeEvent
    }
  }
}

class RecipeRuntime(recipe: CompiledRecipe, interactionManager: InteractionManager, eventStream: EventStream)(implicit ec: ExecutionContext) extends ProcessInstanceRuntime[Place, Transition, ProcessState, RuntimeEvent] {

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

  override val eventSource = recipeEventSourceFn

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
              val runtimeEvent = RuntimeEvent(eventName, Map.empty)
              Continue(createProducedMarking(outMarking, Some(runtimeEvent)), runtimeEvent)
            }
          }

        case _ => BlockTransition
      }
  }

  override def transitionTask(petriNet: PetriNet[Place, Transition], t: Transition)(marking: Marking[Place], state: ProcessState, input: Any): IO[(Marking[Place], RuntimeEvent)] =
    t match {
      case interaction: InteractionTransition => interactionTask(interaction, petriNet.outMarking(t), state)
      case t: EventTransition                 => IO.pure(petriNet.outMarking(t).toMarking, input.asInstanceOf[RuntimeEvent])
      case t                                  => IO.pure(petriNet.outMarking(t).toMarking, null.asInstanceOf[RuntimeEvent])
    }

  def interactionTask(interaction: InteractionTransition,
                      outAdjacent: MultiSet[Place],
                      processState: ProcessState): IO[(Marking[Place], RuntimeEvent)] = {

    // returns a delayed task that will get executed by the process instance
    IO.fromFuture(IO {

      // add MDC values for logging
      MDC.put("processId", processState.processId)
      MDC.put("recipeName", recipe.name)

      try {

        // obtain the interaction implementation
        val implementation = interactionManager.getImplementation(interaction).getOrElse {
          throw new FatalInteractionException("No implementation available for interaction")
        }

        // create the interaction input
        val input = createInteractionInput(interaction, processState)

        val timeStarted = System.currentTimeMillis()

        // publish the fact that we started the interaction
        eventStream.publish(InteractionStarted(timeStarted, recipe.name, recipe.recipeId, processState.processId, interaction.interactionName))

        // executes the interaction and obtain the (optional) output event
        implementation.execute(input).map { interactionOutput =>

          // validates the event, throws a FatalInteraction exception if invalid
          RecipeRuntime.validateInteractionOutput(interaction, interactionOutput).foreach { validationError =>
            throw new FatalInteractionException(validationError)
          }

          // transform the event if there is one
          val outputEvent: Option[RuntimeEvent] = interactionOutput
            .map(e => transformInteractionEvent(interaction, e))

          val timeCompleted = System.currentTimeMillis()

          // publish the fact that the interaction completed
          eventStream.publish(InteractionCompleted(timeCompleted, timeCompleted - timeStarted, recipe.name, recipe.recipeId, processState.processId, interaction.interactionName, outputEvent))

          // create the output marking for the petri net
          val outputMarking: Marking[Place] = RecipeRuntime.createProducedMarking(outAdjacent, outputEvent)

          (outputMarking, outputEvent.orNull)
        }

      } finally {
        // remove the MDC values
        MDC.remove("processId")
        MDC.remove("recipeName")
      }

    }).handleErrorWith {
      case e: InvocationTargetException => IO.raiseError(e.getCause)
      case e: Throwable                 => IO.raiseError(e)
    }
  }
}
