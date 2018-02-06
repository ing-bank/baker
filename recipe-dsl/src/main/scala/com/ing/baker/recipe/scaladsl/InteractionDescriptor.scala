package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common._
import com.ing.baker.types.Converters

object InteractionDescriptorFactory {
  def apply(interaction: Interaction): InteractionDescriptor = InteractionDescriptor(interaction)
  def apply(interaction: Interaction, name: String): InteractionDescriptor = InteractionDescriptor(interaction, newName = name)
}

case class InteractionDescriptor private(override val interaction: Interaction,
                                         override val requiredEvents: Set[String] = Set.empty,
                                         override val requiredOneOfEvents: Set[Set[String]] = Set.empty,
                                         override val predefinedIngredients: Map[String, com.ing.baker.types.Value] = Map.empty,
                                         override val overriddenIngredientNames: Map[String, String] = Map.empty,
                                         override val overriddenOutputIngredientName: Option[String] = None,
                                         override val maximumInteractionCount: Option[Int] = None,
                                         override val failureStrategy: Option[InteractionFailureStrategy] = None,
                                         override val eventOutputTransformers: Map[common.Event, common.EventOutputTransformer] = Map.empty,
                                         newName: String = null)
  extends common.InteractionDescriptor {

  override val name: String = {
    if (newName != null) newName
    else interaction.name
  }

  def withRequiredEvent(event: common.Event): InteractionDescriptor =
    copy(requiredEvents = requiredEvents + event.name)

  def withRequiredEvents(events: common.Event*): InteractionDescriptor =
    copy(requiredEvents = requiredEvents ++ events.map(_.name))

  def withRequiredOneOfEvents(newRequiredOneOfEvents: common.Event*): InteractionDescriptor = {
    if (newRequiredOneOfEvents.nonEmpty && newRequiredOneOfEvents.size < 2)
      throw new IllegalArgumentException("At least 2 events should be provided as 'requiredOneOfEvents'")

    val newRequired: Set[Set[String]] = requiredOneOfEvents + newRequiredOneOfEvents.map(_.name).toSet

    copy(requiredOneOfEvents = newRequired)
  }

  def withPredefinedIngredients(values: (String, AnyRef)*): InteractionDescriptor =
    withPredefinedIngredients(values.toMap)

  def withPredefinedIngredients(data: Map[String, AnyRef]): InteractionDescriptor =
    copy(predefinedIngredients = predefinedIngredients ++ data.map{case (key, value) => key -> Converters.toValue(value)})

  def withMaximumInteractionCount(n: Int): InteractionDescriptor =
    copy(maximumInteractionCount = Some(n))

  def withFailureStrategy(failureStrategy: InteractionFailureStrategy) = copy(failureStrategy = Some(failureStrategy))

  def withOverriddenIngredientName(oldIngredient: String,
                                   newIngredient: String): InteractionDescriptor =
    copy(overriddenIngredientNames = overriddenIngredientNames + (oldIngredient -> newIngredient))

  def withOverriddenOutputIngredientName(newIngredientOutputName: String): InteractionDescriptor =
    copy(overriddenOutputIngredientName = Some(newIngredientOutputName))

  def withEventOutputTransformer(event: Event, newEventName: String, ingredientRenames: Map[String, String]): InteractionDescriptor =
    copy(eventOutputTransformers = eventOutputTransformers + (event -> EventOutputTransformer(newEventName, ingredientRenames)))
}
