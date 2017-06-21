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

class TaskProvider(interactionProviders: Map[String, () => AnyRef]) extends TransitionTaskProvider[ProcessState, Place, Transition] {

  val log = LoggerFactory.getLogger(classOf[TaskProvider])

  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking

  override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] = {
    t match {
      case interaction: InteractionTransition[_] =>
        interactionTransitionTask[AnyRef, Input, Output](interaction.asInstanceOf[InteractionTransition[AnyRef]], interactionProviders(interaction.originalInteractionName), petriNet.outMarking(interaction))
      case t: EventTransition  => eventTransitionTask(petriNet, t)
      case t                   => passThroughtTransitionTask(petriNet, t)
    }
  }

  def passThroughtTransitionTask[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, ProcessState] =
    (consume, processState, input) => Task.now((toMarking[Place](petriNet.outMarking(t)), null.asInstanceOf[Output]))

  def eventTransitionTask[RuntimeEvent, Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], eventTransition: EventTransition): TransitionTask[Place, Input, Output, ProcessState] =
    (consume, processState, input) => Task.now((toMarking[Place](petriNet.outMarking(eventTransition)), input.asInstanceOf[Output]))

  def interactionTransitionTask[I, Input, Output](interaction: InteractionTransition[I], interactionProvider: () => I, outAdjacent: MultiSet[Place[_]]): TransitionTask[Place, Input, Output, ProcessState] =

    (consume, processState, input) => {

    def failureHandler[T]: PartialFunction[Throwable, Task[T]] = {
      case e: InvocationTargetException => Task.fail(e.getCause)
      case e: Throwable => Task.fail(e)
    }

    Try {
      val inputArgs = createMethodInput(interaction, processState)
      val invocationId = UUID.randomUUID().toString
      val interactionObject: I = interactionProvider.apply()

      log.trace(
        s"[$invocationId] invoking '${interaction.originalInteractionName}' with parameters ${inputArgs.toString}")

      def invokeMethod(): AnyRef = {
        MDC.put("processId", processState.id.toString)
        val result = interactionObject.getClass.getMethod("apply", interaction.inputFields.map(_._2): _*) .invoke(interactionObject, inputArgs: _*)
        log.trace(s"[$invocationId] result: $result")

        MDC.remove("processId")
        result
      }

      def createRuntimeEvent(output: Any): RuntimeEvent = {
        interaction.providesType match {
          case FiresOneOfEvents(_, originalEvents) =>
          {
            val optionalFoundEvent: Option[CompiledEvent] = originalEvents.find(e => e.name equals output.getClass.getSimpleName)
            if (optionalFoundEvent.isDefined)
              RuntimeEvent.forEvent(output, optionalFoundEvent.get)
            else {
              val msg: String = s"Output: $output fired by an interaction but could not link it to any known event for the interaction"
              log.error(msg)
              throw new FatalBakerException(msg)
            }
          }
          case ProvidesIngredient(ingredient) => RuntimeEvent.forIngredient(interaction.interactionName, output, ingredient)
          case ProvidesNothing => RuntimeEvent.forNothing(interaction.interactionName)
        }
      }

      // function that (optionally) transforms the output event using the event output transformers
      def transformEvent(runtimeEvent: RuntimeEvent): RuntimeEvent = {
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

      // returns a delayed task that will get executed by the kagera runtime
      Task
        .delay(invokeMethod())
        .map(createRuntimeEvent)
        .map(transformEvent)
        .map { output => (createProducedMarking(interaction, outAdjacent)(output), output.asInstanceOf[Output]) }
        .handleWith(failureHandler)
    }.recover(failureHandler).get
  }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createMethodInput[A](interaction: InteractionTransition[A], state: ProcessState): Seq[AnyRef] = {

    // We support both UUID and String types
    val processId: Option[(String, AnyRef)] = interaction.inputFields.toMap.get(processIdName).map {
      case c if c == classOf[String] => state.id.toString
      case c if c == classOf[java.util.UUID] => state.id
      case _ => throw new IllegalStateException("Type not supported")
    }.map(value => processIdName -> value)

    // parameterNamesToValues overwrites mapped token values which overwrites context map (in order of importance)
    val argumentNamesToValues: Map[String, Any] = interaction.predefinedParameters ++ processId ++ state.ingredients


    def notFound = (name: String) => {
      log.warn(
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Required input   : ${interaction.inputFieldNames.toSeq.sorted.mkString(",")}
           |Provided input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin)
      throw new IllegalArgumentException(s"Missing parameter: $name")
    }

    // map the values to the input places, throw an error if a value is not found
    val methodInput: Seq[Any] =
      interaction.inputFieldNames.map(i =>
        argumentNamesToValues.getOrElse(i, notFound))

    methodInput.map(_.asInstanceOf[AnyRef])
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
