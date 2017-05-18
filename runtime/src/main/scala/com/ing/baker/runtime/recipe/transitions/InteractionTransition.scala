package com.ing.baker.runtime.recipe.transitions

import java.lang.reflect._
import java.util.UUID

import com.ing.baker.runtime.core.ProcessState
import com.ing.baker.runtime.recipe._
import com.ing.baker.runtime.recipe.duplicates.ReflectionHelpers._
import com.ing.baker.runtime.recipe.duplicates.{ActionType, EventOutputTransformer, InteractionFailureStrategy}
import com.ing.baker.runtime.recipe.ingredientExtractors.IngredientExtractor
import fs2.Task
import io.kagera.api.colored._
import io.kagera.api.multiset._
import org.slf4j._

import scala.util._

/**
  * Kagera Petri Net transition which executes an interaction.
  *
  * @param interactionClass     The interaction class to which the created transition belongs.
  * @param interactionProvider  The provider of the implementation.
  * @param predefinedParameters An extra map from parameter name to parameter value to provide to the action.
  */
case class InteractionTransition[A](
                                     method: Method,
                                     providesIngredient: Boolean,
                                     providesEvent: Boolean,
                                     //Original values of the Interaction
                                     inputFields: Seq[(String, Class[_])],
                                     interactionClass: Class[A],

                                     var interactionProvider: () => A,
                                     interactionName: String,

                                     interactionOutputName: String,
                                     outputEventClasses: Seq[Class[_]],
                                     actionType: ActionType = ActionType.InteractionAction,

                                     //Changes to the original interaction
                                     predefinedParameters: Map[String, Any],
                                     maximumInteractionCount: Option[Int],
                                     failureStrategy: InteractionFailureStrategy,
                                     eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty,

                                     //Technical parameters
                                     ingredientExtractor: IngredientExtractor

                                   )
  extends Transition[Unit, AnyRef, ProcessState] {

  val log: Logger = LoggerFactory.getLogger(classOf[InteractionTransition[_]])

  override val id: Long = interactionName.hashCode.toLong

  override val label: String = interactionName

  override val isAutomated = true

  override def toString: String = label


  // all the input fields of the method
  val inputFieldNames: Seq[String] = inputFields.map(_._1)

  // the input fields for which places need to be created
  val requiredIngredientNames: Set[String] = inputFieldNames.toSet - processIdName -- predefinedParameters.keySet

  val requiredIngredients: Map[String, Class[_]] =
    inputFields.toMap.filterKeys(requiredIngredientNames.contains)

  /**
    * The ingredient or event output type of the interaction
    */
  val outputType: Class[_] = {
    val returnType =
      if (method.isAsynchronous) method.getFirstTypeParameter else method.getReturnType

    if (providesEvent)
      transformEventType(returnType) //performing additional rewriting on the output type if this Interaction provides Events
    else
      returnType
  }

  def transformEventType(clazz: Class[_]): Class[_] =
    eventOutputTransformers
      .get(clazz)
      .fold(clazz.asInstanceOf[Class[Any]])(_.targetType.asInstanceOf[Class[Any]])

  val outputIngredient: Option[(String, Class[_])] =
    if (providesIngredient) Some(interactionOutputName -> outputType) else None

  val outputFieldNames: Seq[String] = {
    if (method.isVoid)
      Nil
    else if (providesIngredient)
      Seq(interactionOutputName)
    else
      outputType.getDeclaredFields.map(_.getName).toSeq
  }

  def matchingEventName(output: AnyRef): String =
    outputEventClasses.find(_.isInstance(output)).map(_.getSimpleName).getOrElse {
      throw new IllegalStateException(
        s"Method output: $output is not an instance of any of the specified event classes: ${
          outputEventClasses
            .mkString(",")
        }")
    }

  override val exceptionStrategy: TransitionExceptionHandler =
    InteractionFailureStrategy.asTransitionExceptionHandler(failureStrategy)

  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    */
  def createProducedMarking(outAdjacent: MultiSet[Place[_]]): AnyRef => Marking = { output =>
    outAdjacent.keys.map { place =>
      val value: Any = {
        if (providesEvent)
          matchingEventName(output)
        else
          ()
      }
      place -> MultiSet(value)
    }.toMarking
  }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createMethodInput(state: ProcessState): Seq[AnyRef] = {

    // We support both UUID and String types
    val processId: Option[(String, AnyRef)] = method.processIdClass.map {
      case c if c == classOf[String] => state.id.toString
      case c if c == classOf[java.util.UUID] => state.id
      case _ => throw new IllegalStateException("Type not supported")
    }.map(value => processIdName -> value)

    // parameterNamesToValues overwrites mapped token values which overwrites context map (in order of importance)
    val argumentNamesToValues = predefinedParameters ++ processId ++ state.ingredients

    // throw an exception when a field is missing
    (inputFieldNames.toSet -- argumentNamesToValues.keySet).foreach { name =>
      log.warn(
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Provided input   : ${inputFieldNames.toSeq.sorted.mkString(",")}
           |Required input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin)
      throw new IllegalArgumentException(s"Missing parameter: $name")
    }

    val parameterIndicesWithValues = argumentNamesToValues.map {
      case (argumentName, argumentValue) => (inputFieldNames.indexWhere(_ == argumentName), argumentValue)
    }.filterMissingParameters

    val sortedIndicesAndValues = parameterIndicesWithValues.sortBy {
      case (index, tokenValue) => index
    }

    val parameterValues = sortedIndicesAndValues.map {
      case (index, tokenValue) => tokenValue.asInstanceOf[AnyRef]
    }

    parameterValues
  }

  override def apply(
                      inAdjacent: MultiSet[Place[_]],
                      outAdjacent: MultiSet[Place[_]]): (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
    (consume, processState, input) => {

      def failureHandler[T]: PartialFunction[Throwable, Task[T]] = {
        case e: InvocationTargetException => Task.fail(e.getCause)
        case e: Throwable => Task.fail(e)
      }

      Try {
        val inputArgs = createMethodInput(processState)
        val invocationId = UUID.randomUUID().toString
        val interactionObject: A = interactionProvider.apply()

        log.trace(
          s"[$invocationId] invoking '${interactionClass.getSimpleName}.${method.getName}' with parameters ${input.toString}")

        def invokeMethod(): AnyRef = {
          MDC.put("processId", processState.id.toString)

          val result = method.invoke(interactionObject, inputArgs: _*)
          log.trace(s"[$invocationId] result: $result")

          MDC.remove("processId")
          result
        }

        // function that (optionally) transforms the output event using the event output transformers
        val transformEvent: AnyRef => AnyRef = output => {
          if (providesEvent)
            eventOutputTransformers
              .get(output.getClass)
              .fold(output)(_.transform(output).asInstanceOf[AnyRef])
          else output
        }

        // returns a delayed task that will get executed by the kagera runtime
        Task
          .delay(invokeMethod())
          .map {
            transformEvent
          }
          .map { output => (createProducedMarking(outAdjacent)(output), output) }
          .handleWith(failureHandler)
      }.recover(failureHandler).get
    }

  override def updateState: (ProcessState) => (AnyRef) => ProcessState =
    state =>
      event => {
        if (event == null || method.isVoid) state
        else if (providesIngredient)
          state.copy(ingredients = state.ingredients + (outputIngredient.get._1 -> event))
        else if (providesEvent)
          state.copy(ingredients = state.ingredients ++ ingredientExtractor.extractIngredientData(event))
        else state
      }
}
