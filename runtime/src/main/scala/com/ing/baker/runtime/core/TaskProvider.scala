package com.ing.baker.runtime.core

import java.lang.reflect.InvocationTargetException
import java.util.UUID

import com.ing.baker.compiledRecipe._
import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.compiledRecipe.petrinet.{EventTransition, FiresOneOfEvents, InteractionTransition, Place, ProvidesIngredient, ProvidesNothing, Transition}
import com.ing.baker.core.ProcessState
import fs2.Task
import io.kagera.api._
import io.kagera.execution.{TransitionTask, TransitionTaskProvider}
import org.slf4j.{LoggerFactory, MDC}

import scala.util.Try

class TaskProvider(interactionProviders: Map[String, () => AnyRef], ingredientExtractor: IngredientExtractor) extends TransitionTaskProvider[ProcessState, Place, Transition] {

  val log = LoggerFactory.getLogger(classOf[TaskProvider])

  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking

  override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _, _]], t: Transition[Input, Output, ProcessState]): TransitionTask[Place, Input, Output, ProcessState] = {
    t match {
      case interaction: InteractionTransition[_] =>
        interactionTransitionTask[AnyRef, Input, Output](interaction.asInstanceOf[InteractionTransition[AnyRef]], interactionProviders(interaction.originalInteractionName), petriNet.outMarking(interaction))
      case t: EventTransition  => eventTransitionTask(petriNet, t)
      case t                   => passThroughtTransitionTask(petriNet, t)
    }
  }

  def passThroughtTransitionTask[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _, _]], t: Transition[Input, Output, _]): TransitionTask[Place, Input, Output, ProcessState] =
    (consume, processState, input) => Task.now((toMarking[Place](petriNet.outMarking(t)), null.asInstanceOf[Output]))

  def eventTransitionTask[RuntimeEvent, Input, Output](petriNet: PetriNet[Place[_], Transition[_, _, _]], eventTransition: EventTransition): TransitionTask[Place, Input, Output, ProcessState] =
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
          case FiresOneOfEvents(events) =>
          {
            val optionalFoundEvent: Option[CompiledEvent] = events.find(e => e.name equals output.getClass.getSimpleName)
            if (optionalFoundEvent.isDefined)
              RuntimeEvent.forEvent(output, optionalFoundEvent.get, ingredientExtractor)
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
         case FiresOneOfEvents(events) => {
           interaction.eventOutputTransformers.get(runtimeEvent.toCompiledEvent) match {
             case Some(eventOutputTransformer) =>
               RuntimeEvent(
                 eventOutputTransformer.newEventName,
                 runtimeEvent.providedIngredients.map(pi => eventOutputTransformer.ingredientRenames.getOrElse(pi._1, pi._1) -> pi._2))
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
        .map { output => (createProducedMarking(interaction, outAdjacent)(output.asInstanceOf[AnyRef]), output.asInstanceOf[Output]) }
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
    val argumentNamesToValues = interaction.predefinedParameters ++ processId ++ state.ingredients

    // throw an exception when a field is missing
    (interaction.inputFieldNames.toSet -- argumentNamesToValues.keySet).foreach { name =>
      log.warn(
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Required input   : ${interaction.inputFieldNames.toSeq.sorted.mkString(",")}
           |Provided input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin)
      throw new IllegalArgumentException(s"Missing parameter: $name")
    }

    val parameterIndicesWithValues = argumentNamesToValues.map {
      case (argumentName, argumentValue) => (interaction.inputFieldNames.indexWhere(_ == argumentName), argumentValue)
    }.toSeq.filter { case (index, tokenValue) => index >= 0 }

    val sortedIndicesAndValues = parameterIndicesWithValues.sortBy {
      case (index, tokenValue) => index
    }

    val parameterValues = sortedIndicesAndValues.map {
      case (index, tokenValue) => tokenValue.asInstanceOf[AnyRef]
    }

    parameterValues
  }

  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    */
  def createProducedMarking[A](interaction: InteractionTransition[A], outAdjacent: MultiSet[Place[_]]): AnyRef => Marking[Place] = { output =>
    outAdjacent.keys.map { place =>
      val value: Any = {
        interaction.providesType match {
          case FiresOneOfEvents(events) =>
            val outputName =  output.getClass.getSimpleName
            events.find(_.name == outputName).map(_.name).getOrElse {
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
