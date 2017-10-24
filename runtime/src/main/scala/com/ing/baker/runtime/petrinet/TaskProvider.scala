package com.ing.baker.runtime.petrinet

import java.lang.reflect.InvocationTargetException

import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, Transition}
import com.ing.baker.il.{IngredientType, autoBoxClasses, getRawClass, processIdName}
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.{TransitionTask, TransitionTaskProvider}
import com.ing.baker.runtime.core.Baker.eventExtractor
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}
import fs2.Task
import org.slf4j.{LoggerFactory, MDC}

import scala.util.Try

class TaskProvider(recipeName: String, interactionManager: InteractionManager) extends TransitionTaskProvider[ProcessState, Place, Transition] {

  val log = LoggerFactory.getLogger(classOf[TaskProvider])

  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking

  override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] = {
    t match {
      case interaction: InteractionTransition[_] =>
        interactionTransitionTask[AnyRef, Input, Output](interaction.asInstanceOf[InteractionTransition[AnyRef]], interactionManager, petriNet.outMarking(interaction))
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
    interaction.eventOutputTransformers
      .find { case (eventType, _) => runtimeEvent.isInstanceOfEventType(eventType) } match {
      case Some((_, eventOutputTransformer)) =>
        RuntimeEvent(
          eventOutputTransformer.newEventName,
          runtimeEvent.providedIngredients.map { case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
      case None => runtimeEvent
    }
  }

  def interactionTransitionTask[I, Input, Output](interaction: InteractionTransition[I], interactionManager: InteractionManager, outAdjacent: MultiSet[Place[_]]): TransitionTask[Place, Input, Output, ProcessState] =

    (_, processState, _) => {

    def failureHandler[T]: PartialFunction[Throwable, Task[T]] = {
      case e: InvocationTargetException => Task.fail(e.getCause)
      case e: Throwable => Task.fail(e)
    }

    Try {
      // returns a delayed task that will get executed by the baker petrinet runtime

      Task
        .delay {
          // add MDC values for logging
          MDC.put("processId", processState.processId.toString)
          MDC.put("recipeName", recipeName)

          // create the interaction input
          val input = createInput(interaction, processState)

          // execute the interaction
//          val output = fn.apply(input)

          //TODO move the error scenario away from this location
          val output = interactionManager.getInteractionImplementation(interaction).get.execute(input)

          // create a runtime event from the interaction output
          val event = createRuntimeEvent(interaction, output)

          // transforms the event
          val transformedEvent = transformEvent(interaction)(event)

          // creates the transition output marking (in the petri net)
          val outputMarking = createProducedMarking(interaction, outAdjacent)(transformedEvent)

          // remove MDC values
          MDC.remove("processId")
          MDC.remove("recipeName")

          (outputMarking, transformedEvent.asInstanceOf[Output])
        }
        .handleWith(failureHandler)
    }.recover(failureHandler).get
  }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createInput[A](interaction: InteractionTransition[A], state: ProcessState): Seq[AnyRef] = {

    // We do not support any other type then String types
    val processId: (String, String) = processIdName -> state.processId.toString

    // parameterNamesToValues overwrites mapped token values which overwrites context map (in order of importance)
    val argumentNamesToValues: Map[String, Any] = interaction.predefinedParameters ++ state.ingredients + processId

    def throwMissingInputException = (name: String) => {
      val msg =
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Required input   : ${interaction.requiredIngredients.toMap.keySet.toSeq.sorted.mkString(",")}
           |Provided input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin
      log.warn(msg)
      throw new IllegalArgumentException(msg)
    }

    def autoBoxIfNeeded(ingredientName: String, ingredientType: java.lang.reflect.Type, value: Any) = {
      val ingredientClass = getRawClass(ingredientType)

      if (autoBoxClasses.contains(ingredientClass) && !ingredientClass.isAssignableFrom(value.getClass))
        autoBoxClasses(ingredientClass).apply(value)
      else
        value
    }

    // map the values to the input places, throw an error if a value is not found
    val methodInput: Seq[Any] =
      interaction.requiredIngredients.map {
        case (ingredientName, ingredientType) =>

          val value = argumentNamesToValues.getOrElse(ingredientName, throwMissingInputException)
          autoBoxIfNeeded(ingredientName, ingredientType, value)
      }

    methodInput.map(_.asInstanceOf[AnyRef])
  }

  def createRuntimeEvent[I](interaction: InteractionTransition[I], output: Any): RuntimeEvent = {

    // when the interaction does not fire an event, Void or Unit is a valid output type
    if (interaction.eventsToFire.isEmpty && (output.isInstanceOf[Void] || output.isInstanceOf[Unit]))
      RuntimeEvent(interaction.interactionName, Seq.empty)
    // if the interaction directly produces an ingredient
    else if (interaction.providedIngredientEvent.isDefined) {
      val eventToComplyTo = interaction.providedIngredientEvent.get
      runtimeEventForIngredient(interaction, eventToComplyTo.name, output, eventToComplyTo.ingredientTypes.head)
    }
    else {
      val runtimeEvent = eventExtractor.extractEvent(output)

      val nullIngredientNames = runtimeEvent.providedIngredients.collect {
        case (name, null) => name
      }

      if(nullIngredientNames.nonEmpty) {
        val msg: String = s"Interaction ${interaction.interactionName} returned null value for ingredients: ${nullIngredientNames.mkString(",")}"
        log.error(msg)
        throw new FatalInteractionException(msg)
      }

      if (interaction.originalEvents.exists(runtimeEvent.isInstanceOfEventType))
        runtimeEvent

      else {
        val msg: String = s"Output: $output fired by interaction ${interaction.interactionName} but could not link it to any known event for the interaction"
        log.error(msg)
        throw new FatalInteractionException(msg)
      }
    }
  }

  def runtimeEventForIngredient[I](interaction: InteractionTransition[I], runtimeEventName: String, providedIngredient: Any, ingredientToComplyTo: IngredientType): RuntimeEvent = {
    if (providedIngredient == null) {
      val msg: String = s"null value provided for ingredient '${ingredientToComplyTo.name}' for interaction '${interaction.interactionName}'"
      log.error(msg)
      throw new FatalInteractionException(msg)
    }

    if (ingredientToComplyTo.clazz.isAssignableFrom(providedIngredient.getClass))
      RuntimeEvent(runtimeEventName , Seq((ingredientToComplyTo.name, providedIngredient)))
    else {
      throw new FatalInteractionException(
        s"""
           |Ingredient: ${ingredientToComplyTo.name} provided by an interaction but does not comply to the expected type
           |Expected  : ${ingredientToComplyTo.javaType}
           |Provided  : $providedIngredient
         """.stripMargin)
    }
  }
}
