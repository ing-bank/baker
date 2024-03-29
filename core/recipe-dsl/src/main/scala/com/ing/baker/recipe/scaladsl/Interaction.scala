package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.{common, javadsl}
import com.ing.baker.recipe.common._
import com.ing.baker.types.Converters

import com.ing.baker.types.mirror

import scala.language.experimental.macros
import scala.reflect.runtime.universe.TypeTag

import scala.collection.immutable.Seq

object Interaction {

  def apply[T : TypeTag]: common.InteractionDescriptor = {
    val runtimeClass = mirror.runtimeClass(mirror.typeOf[T])
    javadsl.interactionClassToCommonInteraction(runtimeClass, None)
  }
}

case class Interaction private(override val name: String,
                               override val inputIngredients: Seq[common.Ingredient],
                               override val output: Seq[common.Event],
                               override val requiredEvents: Set[String] = Set.empty,
                               override val requiredOneOfEvents: Set[Set[String]] = Set.empty,
                               override val predefinedIngredients: Map[String, com.ing.baker.types.Value] = Map.empty,
                               override val overriddenIngredientNames: Map[String, String] = Map.empty,
                               override val overriddenOutputIngredientName: Option[String] = None,
                               override val maximumInteractionCount: Option[Int] = None,
                               override val failureStrategy: Option[InteractionFailureStrategy] = None,
                               override val eventOutputTransformers: Map[common.Event, common.EventOutputTransformer] = Map.empty,
                               override val isReprovider: Boolean = false,
                               oldName: Option[String] = None,
                              )
  extends common.InteractionDescriptor {

  override val originalName: String = oldName.getOrElse(name)

  def withName(newName: String): Interaction = copy(name = newName, oldName = Some(name))

  def withRequiredEvent(event: common.Event): Interaction =
    copy(requiredEvents = requiredEvents + event.name)

  def withRequiredEvents(events: common.Event*): Interaction =
    copy(requiredEvents = requiredEvents ++ events.map(_.name))

  def withRequiredOneOfEvents(newRequiredOneOfEvents: common.Event*): Interaction = {
    if (newRequiredOneOfEvents.nonEmpty && newRequiredOneOfEvents.size < 2)
      throw new IllegalArgumentException("At least 2 events should be provided as 'requiredOneOfEvents'")

    val newRequired: Set[Set[String]] = requiredOneOfEvents + newRequiredOneOfEvents.map(_.name).toSet

    copy(requiredOneOfEvents = newRequired)
  }

  def withPredefinedIngredients(values: (String, Any)*): Interaction =
    withPredefinedIngredients(values.toMap)

  def withPredefinedIngredients(data: Map[String, Any]): Interaction =
    copy(predefinedIngredients = predefinedIngredients ++ data.map{case (key, value) => key -> Converters.toValue(value)})

  def withMaximumInteractionCount(n: Int): Interaction =
    copy(maximumInteractionCount = Some(n))

  def withFailureStrategy(failureStrategy: InteractionFailureStrategy) = copy(failureStrategy = Some(failureStrategy))

  def withOverriddenIngredientName(oldIngredient: String,
                                   newIngredient: String): Interaction =
    copy(overriddenIngredientNames = overriddenIngredientNames + (oldIngredient -> newIngredient))

  def withEventOutputTransformer(event: common.Event, ingredientRenames: Map[String, String]): Interaction =
    copy(eventOutputTransformers = eventOutputTransformers + (event -> EventOutputTransformer(event.name, ingredientRenames)))

  def withEventOutputTransformer(event: common.Event, newEventName: String, ingredientRenames: Map[String, String]): Interaction =
    copy(eventOutputTransformers = eventOutputTransformers + (event -> EventOutputTransformer(newEventName, ingredientRenames)))

  /**
    * When this interaction is executed it will fill its own interaction places.
    * This is usefull if you want to execute this interaction multiple times without providing the ingredient again.
    * To use this the InteractionDescriptor requires a prerequisite event.
    *
    * @param isReprovider
    * @return
    */
  def isReprovider(isReprovider: Boolean): Interaction =
    this.copy(isReprovider = isReprovider)
}
