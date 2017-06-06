package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common
import com.ing.baker.newrecipe.common.InteractionFailureStrategy
import com.ing.baker.newrecipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.EventOutputTransformer

import scala.concurrent.duration.Duration

case class InteractionDescriptor private(override val interaction: Interaction,
                                         override val requiredEvents: Set[common.Event] = Set.empty,
                                         override val requiredOneOfEvents: Set[common.Event] = Set.empty,
                                         override val predefinedIngredients: Map[String, AnyRef] = Map.empty,
                                         override val overriddenIngredientNames: Map[String, String] = Map.empty,
                                         override val overriddenOutputIngredientName: Option[String] = None,
                                         override val maximumInteractionCount: Option[Int] = None,
                                         override val failureStrategy: Option[InteractionFailureStrategy] = None,
                                         override val eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty)
  extends common.InteractionDescriptor {

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
}

object InteractionDescriptorFactory {
  def apply(interaction: Interaction): InteractionDescriptor = InteractionDescriptor(interaction)
}
