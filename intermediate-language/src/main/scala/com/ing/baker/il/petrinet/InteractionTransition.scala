package com.ing.baker.il.petrinet

import com.ing.baker.il
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.il.{EventOutputTransformer, _}
import com.ing.baker.types.Value
import org.slf4j._


/**
  * A transition that represents an Interaction
  *
  * @tparam I The class/interface of the interaction
  */
case class InteractionTransition(eventsToFire: Seq[EventDescriptor],
                                    originalEvents: Seq[EventDescriptor],
                                    providedIngredientEvent: Option[EventDescriptor],
                                    requiredIngredients: Seq[IngredientDescriptor],
                                    interactionName: String,
                                    originalInteractionName: String,
                                    predefinedParameters: Map[String, Value],
                                    maximumInteractionCount: Option[Int],
                                    failureStrategy: InteractionFailureStrategy,
                                    eventOutputTransformers: Map[String, EventOutputTransformer] = Map.empty)

  extends Transition {

  val log: Logger = LoggerFactory.getLogger(classOf[InteractionTransition])

  override val label: String = interactionName

  override val id: Long = il.sha256HashCode(s"InteractionTransition:$label")

  override def toString: String = label

    /**
    * These are the ingredients that are not pre-defined or processId
    */
  val nonProvidedIngredients: Seq[IngredientDescriptor] =
    requiredIngredients.filterNot(i => i.name == processIdName || predefinedParameters.keySet.contains(i.name))
}
