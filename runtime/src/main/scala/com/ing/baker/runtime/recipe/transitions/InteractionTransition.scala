package com.ing.baker.runtime.recipe.transitions

import java.lang.reflect._
import java.util.UUID

import com.ing.baker.runtime.core.ProcessState
import com.ing.baker.runtime.recipe._
import com.ing.baker.runtime.recipe.duplicates.ReflectionHelpers._
import com.ing.baker.runtime.recipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.runtime.recipe.transitions.ProvidesType._
import fs2.Task
import io.kagera.api.colored._
import io.kagera.api.multiset._
import org.slf4j._

import scala.util._

/**
  * This trait describes what kind of output the interaction provides
  */
sealed trait ProvidesType

object ProvidesType {

  /**
    * the interaction provides an ingredient
    * @param outputIngredient the ingredient the interaction provides
    * @param outputType the class of the ingredient that the interaction provides
    */
  case class ProvidesIngredient(outputIngredient: (String, Class[_]),
                                outputType: Class[_]
                               ) extends ProvidesType

  /**
    * The interaction provides an event
    * @param outputFieldNames
    * @param outputType the class that the event that is returned
    * @param outputEventClasses the different events that the Interaction can provide
    */
  case class ProvidesEvent(outputFieldNames: Seq[String],
                           outputType: Class[_],
                           outputEventClasses: Seq[Class[_]]
                          ) extends ProvidesType

  case object ProvidesNothing extends ProvidesType

}

/**
  * A transition that represents an Interaction
  * @param method
  * @param providesType
  * @param inputFields
  * @param interactionClass
  * @param interactionProvider
  * @param interactionName
  * @param actionType
  * @param predefinedParameters
  * @param maximumInteractionCount
  * @param failureStrategy
  * @param eventOutputTransformers
  * @param ingredientExtractor
  * @tparam A
  */
case class InteractionTransition[A](
                                     //Original values of the Interaction
                                     method: Method,
                                     providesType: ProvidesType,
                                     inputFields: Seq[(String, Class[_])],
                                     interactionClass: Class[A],
                                     var interactionProvider: () => A,
                                     interactionName: String,
                                     actionType: ActionType = ActionType.InteractionAction,

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

  def transformEventType(clazz: Class[_]): Class[_] =
  eventOutputTransformers
    .get(clazz)
    .fold(clazz.asInstanceOf[Class[Any]])(_.targetType.asInstanceOf[Class[Any]])

  def matchingEventName(output: AnyRef): String =
    providesType match {
      case ProvidesEvent(_, _, outputEventClasses: Seq[Class[_]]) =>
        outputEventClasses.find(_.isInstance(output)).map(_.getSimpleName).getOrElse {
          throw new IllegalStateException(
            s"Method output: $output is not an instance of any of the specified event classes: ${
              outputEventClasses
                .mkString(",")
            }")
        }
      case _ => ""
    }

  override val exceptionStrategy: TransitionExceptionHandler =
    InteractionFailureStrategy.asTransitionExceptionHandler(failureStrategy)

  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    */
  def createProducedMarking(outAdjacent: MultiSet[Place[_]]): AnyRef => Marking = { output =>
    outAdjacent.keys.map { place =>
      val value: Any = {
        providesType match {
          case ProvidesEvent(_, _, _) => matchingEventName(output)
          case _ => ()
        }
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
          providesType match {
            case ProvidesEvent(_, _, _) =>
              eventOutputTransformers
                .get(output.getClass)
                .fold(output)(_.transform(output).asInstanceOf[AnyRef])
            case _ => output
          }
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
        providesType match {
          case _ if event == null => state
          case ProvidesIngredient(outputIngredient: (String, Class[_]), _) =>
            state.copy(ingredients = state.ingredients + (outputIngredient._1 -> event))
          case ProvidesEvent(_, _, _) =>
            state.copy(ingredients = state.ingredients ++ ingredientExtractor.extractIngredientData(event))
          case ProvidesNothing => state
          case _ => state
        }
      }
}
