package com.ing.baker.il.petrinet

import com.ing.baker.il
import com.ing.baker.il.CompiledRecipe.RecipeIdVariant
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.il.{EventOutputTransformer, _}
import com.ing.baker.types.Value
import org.slf4j._

import scala.collection.immutable.Seq

/**
  * A transition that represents an Interaction
  */
case class InteractionTransition(eventsToFire: Seq[EventDescriptor],
                                 originalEvents: Seq[EventDescriptor],
                                 requiredIngredients: Seq[IngredientDescriptor],
                                 interactionName: String,
                                 originalInteractionName: String,
                                 predefinedParameters: Map[String, Value],
                                 maximumInteractionCount: Option[Int],
                                 failureStrategy: InteractionFailureStrategy,
                                 eventOutputTransformers: Map[String, EventOutputTransformer] = Map.empty)

  extends Transition with HasCustomToStringForRecipeId {

  override val label: String = interactionName

  override val id: Long = il.sha256HashCode(s"InteractionTransition:$label")

    /**
    * These are the ingredients that are not pre-defined or recipeInstanceId
    */
  val nonProvidedIngredients: Seq[IngredientDescriptor] =
    requiredIngredients.filterNot(i => i.name == recipeInstanceIdName || predefinedParameters.keySet.contains(i.name))

  override def toStringForRecipeId(recipeIdVariant: RecipeIdVariant): String =
    s"InteractionTransition(${eventsToFire.toRecipeIdStringTypeA(recipeIdVariant)},${originalEvents.toRecipeIdStringTypeA(recipeIdVariant)}," +
      s"${requiredIngredients.toRecipeIdStringTypeB(recipeIdVariant)},$interactionName,$originalInteractionName," +
      s"$predefinedParameters,$maximumInteractionCount,$failureStrategy,$eventOutputTransformers)"
}
