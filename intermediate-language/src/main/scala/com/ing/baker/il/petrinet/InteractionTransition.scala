package com.ing.baker.il.petrinet

import java.lang.reflect.Type

import com.ing.baker.il
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.il.{ActionType, EventOutputTransformer, _}
import com.ing.baker.petrinet.runtime.TransitionExceptionHandler
import org.slf4j._

/**
  * This trait describes what kind of output the interaction provides
  */
sealed trait ProvidesType
case class ProvidesIngredient(ingredient: IngredientType) extends ProvidesType
case class FiresOneOfEvents(events: Seq[EventType], originalEvents: Seq[EventType]) extends ProvidesType
case object ProvidesNothing extends ProvidesType



/**
  * A transition that represents an Interaction
  *
  * @tparam I The class/interface of the interaction
  */
case class InteractionTransition[I](providesType: ProvidesType,
                                    requiredIngredients: Seq[(String, Type)],
                                    interactionName: String,
                                    originalInteractionName: String,
                                    actionType: ActionType = ActionType.InteractionAction,
                                    predefinedParameters: Map[String, Any],
                                    maximumInteractionCount: Option[Int],
                                    failureStrategy: InteractionFailureStrategy,
                                    eventOutputTransformers: Map[EventType, EventOutputTransformer] = Map.empty)

  extends Transition[Unit, AnyRef] {

  val log: Logger = LoggerFactory.getLogger(classOf[InteractionTransition[_]])

  override val label: String = interactionName

  override val id: Long = il.sha256HashCode(s"InteractionTransition:$label")

  override def toString: String = label

    /**
    * These are the ingredients that are not pre-defined or processId
    */
  val nonProvidedIngredients: Map[String, Type] = {
    val names = requiredIngredients.toMap.keySet - processIdName -- predefinedParameters.keySet
    requiredIngredients.toMap.filterKeys(names.contains)
  }


  val exceptionStrategy: TransitionExceptionHandler = failureStrategy.asTransitionExceptionHandler()
}
