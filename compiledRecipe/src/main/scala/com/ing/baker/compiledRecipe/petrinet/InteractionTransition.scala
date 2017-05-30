package com.ing.baker.compiledRecipe.petrinet

import java.lang.reflect._

import com.ing.baker.compiledRecipe.{ActionType, EventOutputTransformer, InteractionFailureStrategy, _}
import com.ing.baker.core.ProcessState
import io.kagera.execution.TransitionExceptionHandler
import org.slf4j._

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
  *
  * @param method
  * @param providesType
  * @param inputFields
  * @param interactionClass
  * @param interactionName
  * @param actionType
  * @param predefinedParameters
  * @param maximumInteractionCount
  * @param failureStrategy
  * @param eventOutputTransformers
  *
  * @tparam I The class/interface of the interaction
  */
case class InteractionTransition[I](
                                     //Original values of the Interaction
                                     method: Method,
                                     providesType: ProvidesType,
                                     inputFields: Seq[(String, Class[_])],
                                     interactionClass: Class[I],
                                     interactionName: String,
                                     actionType: ActionType = ActionType.InteractionAction,
                                     predefinedParameters: Map[String, Any],
                                     maximumInteractionCount: Option[Int],
                                     failureStrategy: InteractionFailureStrategy,
                                     eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty)

  extends Transition[Unit, AnyRef, ProcessState] {

  val log: Logger = LoggerFactory.getLogger(classOf[InteractionTransition[_]])

  override val id: Long = (interactionName + "InteractionTransition").hashCode.toLong

  override val label: String = interactionName

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

  val exceptionStrategy: TransitionExceptionHandler = InteractionFailureStrategy.asTransitionExceptionHandler(failureStrategy)
}
