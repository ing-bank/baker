package com.ing.baker.recipe.scaladsl

import scala.concurrent.duration.Duration
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common._
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff

case class InteractionDescriptor private(override val interaction: Interaction,
                                         override val requiredEvents: Set[common.Event] = Set.empty,
                                         override val requiredOneOfEvents: Set[common.Event] = Set.empty,
                                         override val predefinedIngredients: Map[String, AnyRef] = Map.empty,
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
    copy(requiredEvents = requiredEvents + event)

  def withRequiredEvents(events: common.Event*): InteractionDescriptor =
    copy(requiredEvents = requiredEvents ++ events)

  def withRequiredOneOfEvents(requiredOneOfEvents: common.Event*): InteractionDescriptor =
    copy(requiredOneOfEvents = requiredOneOfEvents.toSet)

  def withPredefinedIngredients(values: (String, AnyRef)*): InteractionDescriptor =
    copy(predefinedIngredients = values.toMap)

  def withPredefinedIngredients(data: Map[String, AnyRef]): InteractionDescriptor =
    copy(predefinedIngredients = data)

  def withMaximumInteractionCount(n: Int): InteractionDescriptor =
    copy(maximumInteractionCount = Some(n))

  def withOverriddenIngredientName(oldIngredient: String,
                                   newIngredient: String): InteractionDescriptor =
    copy(overriddenIngredientNames = overriddenIngredientNames + (oldIngredient -> newIngredient))

  def withOverriddenOutputIngredientName(newIngredientOutputName: String): InteractionDescriptor =
    copy(overriddenOutputIngredientName = Some(newIngredientOutputName))

  def withIncrementalBackoffOnFailure(initialDelay: Duration,
                                      backoffFactor: Double = 2.0,
                                      maximumRetries: Int = 50): InteractionDescriptor =
    copy(failureStrategy = Some(RetryWithIncrementalBackoff(initialDelay, backoffFactor, maximumRetries)))

  def withEventOutputTransformer(event: Event, newEventName: String, ingredientRenames: Map[String, String]): InteractionDescriptor =
    copy(eventOutputTransformers = eventOutputTransformers + (event -> EventOutputTransformer(newEventName, ingredientRenames)))
}

object InteractionDescriptorFactory {
  def apply(interaction: Interaction): InteractionDescriptor = InteractionDescriptor(interaction)
  def apply(interaction: Interaction, name: String): InteractionDescriptor = InteractionDescriptor(interaction, newName = name)
}
