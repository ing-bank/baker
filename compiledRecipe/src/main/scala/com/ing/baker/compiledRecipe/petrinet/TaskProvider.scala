package com.ing.baker.compiledRecipe.petrinet

import java.lang.reflect.InvocationTargetException
import java.util.UUID

import com.ing.baker.compiledRecipe._
import com.ing.baker.compiledRecipe.duplicates.ReflectionHelpers._
import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.compiledRecipe.petrinet.ProvidesType.ProvidesEvent
import com.ing.baker.core.ProcessState
import fs2.Task
import io.kagera.api._
import io.kagera.execution.{TransitionTask, TransitionTaskProvider}
import org.slf4j.{LoggerFactory, MDC}

import scala.util.Try

class TaskProvider(interactionProviders: Map[Class[_], () => AnyRef], ingredientExtractor: IngredientExtractor) extends TransitionTaskProvider[ProcessState, Place, Transition] {

  val log = LoggerFactory.getLogger(classOf[TaskProvider])

  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking

  override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _, _]], t: Transition[Input, Output, ProcessState]): TransitionTask[Place, Input, Output, ProcessState] = {
    t match {
      case interaction: InteractionTransition[_] =>
        interactionTransitionTask[AnyRef, Input, Output](interaction.asInstanceOf[InteractionTransition[AnyRef]], interactionProviders(interaction.interactionClass), petriNet.outMarking(interaction))
      case t: EventTransition[_]         => eventTransitionTask(petriNet, t)
      case t                             => passThroughtTransitionTask(petriNet, t)
    }
  }

  def passThroughtTransitionTask[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _, _]], t: Transition[Input, Output, _]): TransitionTask[Place, Input, Output, ProcessState] =
    (consume, processState, input) => Task.now((toMarking[Place](petriNet.outMarking(t)), null.asInstanceOf[Output]))

  def eventTransitionTask[E, Input, Output](petriNet: PetriNet[Place[_], Transition[_, _, _]], eventTransition: EventTransition[E]): TransitionTask[Place, Input, Output, ProcessState] =
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
        s"[$invocationId] invoking '${interaction.interactionClass.getSimpleName}.${interaction.method.getName}' with parameters ${input.toString}")

      def invokeMethod(): AnyRef = {
        MDC.put("processId", processState.id.toString)

        val result = interaction.method.invoke(interactionObject, inputArgs: _*)
        log.trace(s"[$invocationId] result: $result")

        MDC.remove("processId")
        result
      }

      // function that (optionally) transforms the output event using the event output transformers
      def transformEvent: AnyRef => Output = methodOutput => {
        interaction.providesType match {
          case ProvidesEvent(_, _, _) =>
            interaction.eventOutputTransformers
              .get(methodOutput.getClass)
              .map(_.transform(methodOutput))
              .getOrElse(methodOutput).asInstanceOf[Output]
          case _ => methodOutput.asInstanceOf[Output]
        }
      }

      // returns a delayed task that will get executed by the kagera runtime
      Task
        .delay(invokeMethod())
        .map {
          transformEvent
        }
        .map { output => (createProducedMarking(interaction, outAdjacent)(output.asInstanceOf[AnyRef]), output) }
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
    val processId: Option[(String, AnyRef)] = interaction.method.processIdClass.map {
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
           |Provided input   : ${interaction.inputFieldNames.toSeq.sorted.mkString(",")}
           |Required input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin)
      throw new IllegalArgumentException(s"Missing parameter: $name")
    }

    val parameterIndicesWithValues = argumentNamesToValues.map {
      case (argumentName, argumentValue) => (interaction.inputFieldNames.indexWhere(_ == argumentName), argumentValue)
    }.filterMissingParameters

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
          case ProvidesEvent(_, _, _) => interaction.matchingEventName(output)
          case _ => ()
        }
      }
      place -> MultiSet(value)
    }.toMarking
  }
}
