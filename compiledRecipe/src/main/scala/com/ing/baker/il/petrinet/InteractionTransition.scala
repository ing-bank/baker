package com.ing.baker.il.petrinet

import com.ing.baker.il.{ActionType, CompiledEventOutputTransformer, InteractionFailureStrategy, _}
import io.kagera.runtime.TransitionExceptionHandler
import org.slf4j._

/**
  * This trait describes what kind of output the interaction provides
  */
sealed trait ProvidesType
case class ProvidesIngredient(ingredient: CompiledIngredient) extends ProvidesType
case class FiresOneOfEvents(events: Seq[CompiledEvent], originalEvents: Seq[CompiledEvent]) extends ProvidesType
case object ProvidesNothing extends ProvidesType



/**
  * A transition that represents an Interaction
  *
  * @param providesType
  * @param inputFields
  * @param interactionName
  * @param actionType
  * @param predefinedParameters
  * @param maximumInteractionCount
  * @param failureStrategy
  * @param eventOutputTransformers
  *
  * @tparam I The class/interface of the interaction
  */
case class InteractionTransition[I](providesType: ProvidesType,
                                    inputFields: Seq[(String, Class[_])],
                                    interactionName: String,
                                    originalInteractionName: String,
                                    actionType: ActionType = ActionType.InteractionAction,
                                    predefinedParameters: Map[String, Any],
                                    maximumInteractionCount: Option[Int],
                                    failureStrategy: InteractionFailureStrategy,
                                    eventOutputTransformers: Map[CompiledEvent, CompiledEventOutputTransformer] = Map.empty)

  extends Transition[Unit, AnyRef] {

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

  val exceptionStrategy: TransitionExceptionHandler = InteractionFailureStrategy.asTransitionExceptionHandler(failureStrategy)
}
